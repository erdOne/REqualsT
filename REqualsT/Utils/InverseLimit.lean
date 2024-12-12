import REqualsT.Utils.Lemmas

variable {ι : Type*} [Preorder ι] [Nonempty ι] [IsDirected ι (· ≥ ·)]
variable (α : ι → Type*) (f : ∀ i j, i ≤ j → α i → α j)

section Topology

variable [∀ i, TopologicalSpace (α i)]
variable (hf : ∀ i j h, Continuous (f i j h))

include hf in
lemma dense_inverseLimit_of_forall_image_dense
    (s : Set { v : Π i, α i // ∀ i j (h : i ≤ j), f i j h (v i) = v j })
    (hs : ∀ i, Dense ((fun x ↦ (Subtype.val x) i) '' s)) : Dense s := by
  classical
  rw [dense_iff_inter_open]
  rintro U ⟨t, ht, rfl⟩ ⟨x, hx⟩
  obtain ⟨I, u, hu₁, hu₂⟩ := isOpen_pi_iff.mp ht _ hx
  obtain ⟨i, hi⟩ := Finset.exists_le (α := ιᵒᵈ) I
  let U : Set (α i) := ⋂ (j : I), (f _ _ (hi j.1 j.2)) ⁻¹' u _
  have hU : IsOpen U := isOpen_iInter_of_finite fun j ↦ (hu₁ j.1 j.2).1.preimage (hf ..)
  obtain ⟨_, hz₁, z, hz₂, rfl⟩ := dense_iff_inter_open.mp (hs i) U hU
    ⟨x.1 _, by simp [U, x.2, hu₁]⟩
  exact ⟨z, hu₂ (by simpa [U, z.2] using hz₁), hz₂⟩

include hf in
lemma denseRange_inverseLimit {β}
    (g : β → { v : Π i, α i // ∀ i j (h : i ≤ j), f i j h (v i) = v j })
    (hg : ∀ i, DenseRange (fun x ↦ (g x).1 i)) : DenseRange g := by
  refine dense_inverseLimit_of_forall_image_dense α f hf _ fun i ↦ ?_
  rw [← Set.range_comp]
  exact hg _

end Topology

section MittagLeffler

variable (hf₀ : ∀ i, f i i le_rfl = id)
variable (hf : ∀ i j k (hij : i ≤ j) (hjk : j ≤ k), f j k hjk ∘ f i j hij = f i k (hij.trans hjk))
variable {l : ℕ → ι} (hl : Antitone l) (hl' : ∀ x, ∃ n, l n ≤ x)

omit [Nonempty ι] [IsDirected ι (· ≥ ·)] in
include hf₀ hf hl hl' in
theorem nonempty_inverseLimit_of_finite [∀ i, Finite (α i)] [∀ i, Nonempty (α i)] :
    Nonempty { v : Π i, α i // ∀ i j (h : i ≤ j), f i j h (v i) = v j } := by
  classical
  let s₀ (i j) := Set.range (f (l (i + j)) (l i) (hl (i.le_add_right j)))
  have hs₀ (i j k) (h : j ≤ k) : s₀ i k ⊆ s₀ i j := by
    rintro _ ⟨x, rfl⟩
    exact ⟨f _ _ (hl (Nat.add_le_add_left h i)) x, congr_fun (hf _ _ _ _ _) _⟩
  let s (i) : Set (α (l i)) := ⋂ j, s₀ i j
  have hs (i) : ∃ j, s₀ i j = s i :=
    WellFoundedLT.exists_eq_inf (α := Set (α (l i))) ⟨s₀ i, hs₀ i⟩
  have hs' (i) : (s i).Nonempty := by
    obtain ⟨j, hj⟩ := hs i; simpa only [← hj] using Set.range_nonempty _
  have (i) (x : s i) : ∃ y : s (i + 1), x.1 = f _ _ (hl i.le_succ) (y.1) := by
    obtain ⟨x, hx⟩ := x
    obtain ⟨k, hk⟩ := hs (i + 1)
    simp only [Nat.succ_eq_add_one, Subtype.exists, ← hk, exists_prop, s₀,
      Set.mem_range, exists_exists_eq_and]
    simp only [Set.mem_iInter, s] at hx
    obtain ⟨x, rfl⟩ := hx (k + 1)
    exact ⟨f _ _ (hl (by nlinarith)) x,
      (congr_fun (hf _ _ _ _ _) _).symm.trans (congr_fun (hf _ _ _ _ _) _).symm⟩
  choose r hr using this
  obtain ⟨r₀, hr₀⟩ := hs' 0
  let n (i) := Nat.find (hl' i)
  have hn (i) : l (n i) ≤ i := Nat.find_spec (hl' i)
  let seq (i : ℕ) : s i := i.rec ⟨r₀, hr₀⟩ r
  have (i j) : f (l (i + j)) (l i) (hl (i.le_add_right j)) (seq _).1 = (seq _).1 := by
    induction j with
    | zero => simp [hf₀]
    | succ j IH =>
      rw [← IH, ← (hr _ (seq (i + j))).symm]
      exact (congr_fun (hf _ _ _ _ _) _).symm
  replace this (i j) (h : i ≤ j) : f (l j) (l i) (hl h) (seq j).1 = (seq i).1 := by
    obtain ⟨j, rfl⟩ : ∃ k, j = i + k := Nat.exists_eq_add_of_le h; apply this
  refine ⟨⟨fun i ↦ f _ _ (hn _) (seq (n i)).1, fun i j h ↦ ?_⟩⟩
  have hn' : n j ≤ n i := Nat.find_min' _ ((hn i).trans h)
  dsimp only
  rw [← this _ _ hn']
  exact (congr_fun (hf _ _ _ _ _) _).trans (congr_fun (hf _ _ _ _ _) _).symm

end MittagLeffler
