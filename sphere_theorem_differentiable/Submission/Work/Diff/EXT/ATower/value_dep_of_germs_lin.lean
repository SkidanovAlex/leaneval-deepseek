import Mathlib
import Submission.Work.Diff.EXT.ATower.tower_value_defs
import Submission.Commons.Geometry.Manifold.VectorField.exists_frame_decomposition_of_apply_eq_zero

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT.ATower

/-! ### Hints for the prover (supplied piece of `Work.Diff.EXT.ATower.tower_value_dep`)

This is the abstract "germ-local on smooth tuples + `C^∞`-linear in every slot ⟹
value-dependent" step (the smooth-tuple variant of `Work.Diff.EXT.ATower.value_dep_of_germ_lin`,
which is the same statement with a germ hypothesis for *all* tuples; the smooth form is what the
tower can supply, cf. `Work.Diff.EXT.ATower.tvdGermTs`).  Import
`Submission.Commons.Geometry.Manifold.VectorField.exists_frame_decomposition_of_apply_eq_zero`
(the frame decomposition, proved there: a smooth field `X` with `X x = 0` is, near `x`, a finite
combination `∑ i, f i • Y i` of smooth *globally defined* fields `Y i` with smooth coefficients
`f i`, and `f i x = 0`; the index type is `Fin (Module.finrank ℝ E)`).

Suggested route.
1. *Single slot, vanishing field.* For a smooth tuple `F`, a slot `j` and a smooth field `Z` with
   `Z x = 0`: decompose `Z =ᶠ[𝓝 x] ∑ i, f i • Y i`; by `hGerm` (applied to the two smooth tuples
   `update F j Z` and `update F j (∑ i, f i • Y i)`),
   `Φ (Function.update F j Z) x = Φ (Function.update F j (∑ i, f i • Y i)) x`, and by `hLin` at slot
   `j` with `X := Y`, `f := f`, `S := ∑ i, f i • Y i` this is
   `∑ i, f i x * Φ (Function.update F j (Y i)) x = 0` because `f i x = 0`.
2. *Two tuples differing in one slot.* If `F j x = F' j x` and the other slots coincide, then
   `Φ (Function.update F j (F j)) x = Φ (Function.update F j (F' j + (F j - F' j))) x
     = Φ (Function.update F j (F' j)) x + Φ (Function.update F j (F j - F' j)) x` by `hLin` at slot
   `j` with `ι := Fin 2`, coefficients `1` and `1` and fields `F' j` and `F j - F' j` (use
   `Fin.sum_univ_two`); the second term is `0` by Step 1, and `update F j (F' j) = F'`
   when the other slots coincide.
3. *Chain over the slots.* Interpolate: for `m ≤ n` set `G m : Fin n → TF :=
   fun j => if (j : ℕ) < m then F' j else F j`.  Then `G 0 = F`, `G n = F'`
   (`j.isLt`), `G (m+1) = Function.update (G m) ⟨m, _⟩ (F' ⟨m, _⟩)` for `m < n`
   (`Fin.ext` + `omega`), and `G (m+1)`, `G m` differ only in slot `⟨m, _⟩`, with equal values at
   `x`, so Step 2 gives `Φ (G (m+1)) x = Φ (G m) x`.  Induction on `m` (`Nat.le_induction`) closes
   the proof.  All intermediate tuples are smooth (each slot is some `F i` or `F' i`).
   (`n = 0` is a subsingleton case, `funext`.)
-/

set_option linter.unusedSectionVars false

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]

/-- The function-space form and the pointwise form of a finite sum of field multiples agree. -/
theorem tvd_sum_eq_fun {ι : Type*} [Fintype ι] (f : ι → M → ℝ)
    (X : ι → TF (I := I) (M := M)) :
    (∑ i, f i • X i) = fun y : M => ∑ i, f i y • X i y := by
  funext y
  simp [Finset.sum_apply]

/-- `SmE` is closed under finite sums with smooth scalar coefficients. -/
theorem tvd_smE_sum_univ {ι : Type*} [Fintype ι] (f : ι → M → ℝ)
    (X : ι → TF (I := I) (M := M)) (hf : ∀ i, SmF I M (f i)) (hX : ∀ i, SmE I M (X i)) :
    SmE I M (∑ i, f i • X i) := by
  rw [tvd_sum_eq_fun]
  exact tvd_smE_sum Finset.univ f X (fun i _ => hf i) (fun i _ => hX i)

theorem value_dep_of_germs_lin
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
    {n : ℕ} (Φ : (Fin n → (Π y : M, TangentSpace I y)) → M → ℝ)
    (hGerm : ∀ (F F' : Fin n → (Π y : M, TangentSpace I y)) (x : M),
      (∀ j, Work.Diff.EXT.ATower.SmE I M (F j)) →
      (∀ j, Work.Diff.EXT.ATower.SmE I M (F' j)) →
      (∀ j, Filter.EventuallyEq (nhds x) (F j) (F' j)) → Φ F x = Φ F' x)
    (hLin : ∀ (F : Fin n → (Π y : M, TangentSpace I y)) (j : Fin n) (ι : Type) [Fintype ι]
      (X : ι → (Π y : M, TangentSpace I y)) (f : ι → M → ℝ)
      (S : (Π y : M, TangentSpace I y)),
      (∀ i, Work.Diff.EXT.ATower.SmE I M (F i)) →
      (∀ q, Work.Diff.EXT.ATower.SmE I M (X q)) →
      (∀ q, Work.Diff.EXT.ATower.SmF I M (f q)) →
      Work.Diff.EXT.ATower.SmE I M S →
      (∀ y, S y = ∑ q, f q y • X q y) →
      ∀ y, Φ (Function.update F j S) y = ∑ q, f q y * Φ (Function.update F j (X q)) y)
    {F F' : Fin n → (Π y : M, TangentSpace I y)} {x : M}
    (hF : ∀ i, Work.Diff.EXT.ATower.SmE I M (F i))
    (hF' : ∀ i, Work.Diff.EXT.ATower.SmE I M (F' i))
    (h : ∀ i, F i x = F' i x) :
    Φ F x = Φ F' x := by
  classical
  -- ### Step 1: a smooth field vanishing at `x` contributes nothing in any slot.
  have step1 : ∀ (F : Fin n → TF (I := I) (M := M)) (j : Fin n) (Z : TF (I := I) (M := M)),
      (∀ i, SmE I M (F i)) → SmE I M Z → Z x = 0 → Φ (Function.update F j Z) x = 0 := by
    intro F j Z hFs hZ hZx
    obtain ⟨g, Y, hg, hY, hgx, hdec⟩ :=
      Commons.Geometry.Manifold.VectorField.exists_frame_decomposition_of_apply_eq_zero
        (I := I) (M := M) (X := Z) (x := x) hZ hZx
    set S : TF (I := I) (M := M) := ∑ i, g i • Y i with hSdef
    have hS : SmE I M S := by
      rw [hSdef]
      exact tvd_smE_sum_univ g Y (fun i => hg i) (fun i => hY i)
    have h1 : ∀ i, SmE I M ((Function.update F j Z) i) := by
      intro i
      rcases eq_or_ne i j with rfl | hij
      · rw [Function.update_self]; exact hZ
      · rw [Function.update_of_ne hij]; exact hFs i
    have h2 : ∀ i, SmE I M ((Function.update F j S) i) := by
      intro i
      rcases eq_or_ne i j with rfl | hij
      · rw [Function.update_self]; exact hS
      · rw [Function.update_of_ne hij]; exact hFs i
    have h3 : ∀ i, Filter.EventuallyEq (nhds x) ((Function.update F j Z) i)
        ((Function.update F j S) i) := by
      intro i
      rcases eq_or_ne i j with rfl | hij
      · rw [Function.update_self, Function.update_self]; exact hdec
      · rw [Function.update_of_ne hij, Function.update_of_ne hij]
        try exact Filter.EventuallyEq.refl _ _
    have hgerm := hGerm (Function.update F j Z) (Function.update F j S) x h1 h2 h3
    have hrepr : ∀ y : M, S y = ∑ i, g i y • Y i y := by
      intro y
      simp only [hSdef, tvd_sum_eq_fun]
    have hlin := hLin F j (Fin (Module.finrank ℝ E)) Y g S hFs hY hg hS hrepr x
    rw [hgerm, hlin]
    exact Finset.sum_eq_zero (fun i _ => by rw [hgx i, zero_mul])
  -- ### Step 2: replacing one slot by another field with the same value at `x` is free.
  have step2 : ∀ (F : Fin n → TF (I := I) (M := M)) (j : Fin n) (V : TF (I := I) (M := M)),
      (∀ i, SmE I M (F i)) → SmE I M V → V x = F j x →
      Φ (Function.update F j V) x = Φ F x := by
    intro F j V hFs hV hVx
    have hW : SmE I M (F j - V) := tvd_smE_sub (hFs j) hV
    have hWx : (F j - V) x = 0 := by rw [Pi.sub_apply, hVx, sub_self]
    have hz : Φ (Function.update F j (F j - V)) x = 0 := step1 F j (F j - V) hFs hW hWx
    set X : Fin 2 → TF (I := I) (M := M) := ![V, F j - V] with hXdef
    have hXv0 : X 0 = V := by simp [hXdef]
    have hXv1 : X 1 = F j - V := by simp [hXdef]
    have hX : ∀ q, SmE I M (X q) := by
      intro q
      fin_cases q
      · simpa [hXdef] using hV
      · simpa [hXdef] using hW
    have hc : ∀ q : Fin 2, SmF I M (fun _ : M => (1 : ℝ)) := fun _ => tvd_smF_const
    have hrepr : ∀ y : M,
        F j y = ∑ q : Fin 2, (fun _ : Fin 2 => fun _ : M => (1 : ℝ)) q y • X q y := by
      intro y
      rw [Fin.sum_univ_two]
      simp [hXdef]
    have hl := hLin F j (Fin 2) X (fun _ : Fin 2 => fun _ : M => (1 : ℝ)) (F j) hFs hX hc
      (hFs j) hrepr x
    simp only [Fin.sum_univ_two, one_mul] at hl
    rw [Function.update_eq_self] at hl
    have hX0 : Φ (Function.update F j (X 0)) x = Φ (Function.update F j V) x := by rw [hXv0]
    have hX1 : Φ (Function.update F j (X 1)) x = Φ (Function.update F j (F j - V)) x := by
      rw [hXv1]
    rw [hX0, hX1, hz, add_zero] at hl
    exact hl.symm
  -- ### Step 3: interpolate between `F` and `F'`, one slot at a time.
  set G : ℕ → Fin n → TF (I := I) (M := M) :=
    (fun m j => if (j : ℕ) < m then F' j else F j) with hG
  have hG0 : G 0 = F := by
    funext j
    simp [hG]
  have hGn : G n = F' := by
    funext j
    simp [hG, j.isLt]
  have hGsm : ∀ m, ∀ i, SmE I M (G m i) := by
    intro m i
    by_cases hlt : (i : ℕ) < m
    · rw [show G m i = F' i by simp [hG, hlt]]
      exact hF' i
    · rw [show G m i = F i by simp [hG, hlt]]
      exact hF i
  have step3 : ∀ m, m < n → Φ (G (m + 1)) x = Φ (G m) x := by
    intro m hm
    have hupd : Function.update (G m) ⟨m, hm⟩ (F' ⟨m, hm⟩) = G (m + 1) := by
      funext j
      by_cases hjm : j = ⟨m, hm⟩
      · subst hjm
        rw [Function.update_self]
        simp [hG]
      · have hne : (j : ℕ) ≠ m := fun hh => hjm (Fin.ext hh)
        rw [Function.update_of_ne hjm]
        by_cases hlt : (j : ℕ) < m
        · have hlt' : (j : ℕ) < m + 1 := by omega
          simp [hG, hlt, hlt']
        · have hlt' : ¬ ((j : ℕ) < m + 1) := by omega
          simp [hG, hlt, hlt']
    have hvx : (F' ⟨m, hm⟩) x = (G m) ⟨m, hm⟩ x := by
      rw [show G m ⟨m, hm⟩ = F ⟨m, hm⟩ by simp [hG]]
      exact (h ⟨m, hm⟩).symm
    have hs := step2 (G m) ⟨m, hm⟩ (F' ⟨m, hm⟩) (hGsm m) (hF' ⟨m, hm⟩) hvx
    rw [hupd] at hs
    exact hs
  have key : ∀ m, m ≤ n → Φ (G m) x = Φ F x := by
    intro m
    induction m with
    | zero =>
        intro _
        rw [hG0]
    | succ m ih =>
        intro hm
        exact (step3 m (Nat.lt_of_succ_le hm)).trans (ih (Nat.le_of_succ_le hm))
  have hfin : Φ (G n) x = Φ F x := key n le_rfl
  rw [hGn] at hfin
  exact hfin.symm

end Work.Diff.EXT.ATower
