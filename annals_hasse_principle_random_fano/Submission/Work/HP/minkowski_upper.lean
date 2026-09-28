import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.MinkDefs
import Submission.Work.HP.lam_basic
import Submission.Work.HP.MDEstimates.exists_lift_norm
import Submission.Work.HP.MDEstimates.rk_projScale
import Submission.Work.HP.numaux.ker_projScale_inf
import Submission.Work.HP.Lat.detL_basis_gram
import Submission.Work.HP.BCS.shortest_vec

/-!
# Minkowski's second theorem (upper bound)

`Work.HP.minkowski_upper`: there is a constant `K > 0`, depending only on `ι`, such that for every
integral lattice `L ⊆ ℤ^ι`

  `∏_{j < rk L} lam L (j+1) ≤ K * detL L`.

The proof is the classical inductive argument: pick a shortest vector `u ∈ L`, project the lattice
onto `u^⊥` (realised integrally as `projScale u`, which is `‖u‖²` times the orthogonal projection),
and use

* `lam L (j+1) ≤ (2/√3) · lam (projScale u '' L) j / ‖u‖²`  (lifting a shortest basis), and
* `detL (projScale u '' L) = ‖u‖^{2 rk L - 3} · detL L`  (the covolume of the projection).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
open Finset
open scoped BigOperators

namespace Work.HP

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Elementary facts about `toR`, `dotZ`, `dotR` -/

omit [Fintype ι] [DecidableEq ι] in
lemma toR_add (x y : ι → ℤ) : toR (x + y) = toR x + toR y := by
  funext i; simp [toR]

omit [Fintype ι] [DecidableEq ι] in
lemma toR_sub (x y : ι → ℤ) : toR (x - y) = toR x - toR y := by
  funext i; simp [toR]

omit [Fintype ι] [DecidableEq ι] in
lemma toR_smul (m : ℤ) (x : ι → ℤ) : toR (m • x) = (m : ℝ) • toR x := by
  funext i; simp [toR, Pi.smul_apply, smul_eq_mul]

omit [DecidableEq ι] in
lemma toR_sum {κ : Type*} (s : Finset κ) (f : κ → ι → ℤ) :
    toR (∑ i ∈ s, f i) = ∑ i ∈ s, toR (f i) := by
  funext k; simp [toR]

lemma cast_dotZ (x b : ι → ℤ) : ((dotZ x b : ℤ) : ℝ) = dotR (toR x) (toR b) := by
  simp only [dotZ_apply, dotR, toR, Int.cast_sum, Int.cast_mul]

omit [DecidableEq ι] in
lemma dotZ_sub (x y b : ι → ℤ) : dotZ (x - y) b = dotZ x b - dotZ y b := by
  simp only [dotZ_apply, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

@[simp] lemma dotR_add_left (x y z : ι → ℝ) : dotR (x + y) z = dotR x z + dotR y z := by
  simp only [dotR, Pi.add_apply, add_mul, Finset.sum_add_distrib]

@[simp] lemma dotR_sub_left (x y z : ι → ℝ) : dotR (x - y) z = dotR x z - dotR y z := by
  simp only [dotR, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib]

lemma dotR_smul_left (c : ℝ) (x z : ι → ℝ) : dotR (c • x) z = c * dotR x z := by
  simp only [dotR, Pi.smul_apply, smul_eq_mul]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun i _ => by ring

lemma dotR_self_nonneg (x : ι → ℝ) : 0 ≤ dotR x x :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg _

omit [DecidableEq ι] in
lemma dotR_comm (x y : ι → ℝ) : dotR x y = dotR y x :=
  Finset.sum_congr rfl fun i _ => mul_comm _ _

/-! ## `projScale` computations -/

lemma projScale_self (u : ι → ℤ) : projScale u u = 0 := by
  rw [projScale_apply, sub_self]

lemma dotZ_projScale_right (u z : ι → ℤ) : dotZ (projScale u z) u = 0 := by
  rw [projScale_apply, dotZ_sub, dotZ_smul, dotZ_smul]
  ring

lemma toR_projScale (u z : ι → ℤ) (hu0 : u ≠ 0) :
    toR (projScale u z) = ((dotZ u u : ℤ) : ℝ) •
      (toR z - (dotR (toR z) (toR u) / ((dotZ u u : ℤ) : ℝ)) • toR u) := by
  have hne : dotR (toR u) (toR u) ≠ 0 := by
    rw [← cast_dotZ]
    exact ne_of_gt (by rw [← eNorm_sq_eq u]; exact pow_pos (eNorm_pos_of_ne_zero hu0) 2)
  rw [projScale_apply, toR_sub, toR_smul, toR_smul, cast_dotZ, cast_dotZ, smul_sub]
  congr 1
  rw [smul_smul, mul_div_cancel₀ _ hne]

/-! ## Gram matrices of families of real vectors -/

/-- The Gram matrix of a family of real vectors, with respect to the standard inner product. -/
def gmat {κ : Type*} (z : κ → ι → ℝ) : Matrix κ κ ℝ := Matrix.of fun i j => dotR (z i) (z j)

lemma gmat_apply {κ : Type*} (z : κ → ι → ℝ) (i j : κ) : gmat z i j = dotR (z i) (z j) := rfl

/-- `gmat z` is the coordinate matrix times its transpose. -/
lemma gmat_eq_mul_transpose {κ : Type*} (z : κ → ι → ℝ) :
    gmat z = (Matrix.of z) * (Matrix.of z).transpose := by
  ext i j
  simp only [gmat_apply, dotR, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]

/-- Change of family for Gram matrices: if `z' j = ∑ i, T i j • z i` then
`gmat z' = Tᵀ * gmat z * T`. -/
lemma gmat_change {κ κ' : Type*} [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ']
    {z : κ → ι → ℝ} {z' : κ' → ι → ℝ} {T : Matrix κ κ' ℝ}
    (h : ∀ j, z' j = fun k => ∑ i, T i j * z i k) :
    gmat z' = T.transpose * gmat z * T := by
  have hM : Matrix.of z' = T.transpose * Matrix.of z := by
    ext j k
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply]
    exact congrFun (h j) k
  rw [gmat_eq_mul_transpose, gmat_eq_mul_transpose, hM, Matrix.transpose_mul,
    Matrix.transpose_transpose]
  simp only [Matrix.mul_assoc]

/-- `detL` is the square root of the Gram determinant of any `ℤ`-basis, in the `gmat` form. -/
lemma detL_eq_sqrt_gmat {κ : Type*} [Fintype κ] [DecidableEq κ] {L : Submodule ℤ (ι → ℤ)}
    (b : Module.Basis κ ℤ L) : detL L = Real.sqrt (gmat (fun i => toR (b i : ι → ℤ))).det := by
  have h : gmat (fun i => toR (b i : ι → ℤ))
      = Matrix.of (fun i j : κ => ∑ x, (((b i : ι → ℤ) x : ℝ) * ((b j : ι → ℤ) x : ℝ))) := by
    ext i j
    simp only [gmat_apply, dotR, toR, Matrix.of_apply]
  rw [h, Work.HP.Lat.detL_basis_gram L b]

/-- `detL` of the lattice spanned by a linearly independent family. -/
lemma detL_span_gram {κ : Type*} [Fintype κ] [DecidableEq κ] (f : κ → ι → ℤ)
    (hf : LinearIndependent ℤ f) :
    detL (Submodule.span ℤ (Set.range f)) = Real.sqrt (gmat (fun i => toR (f i))).det := by
  rw [detL_eq_sqrt_gmat (L := Submodule.span ℤ (Set.range f)) (Module.Basis.span hf)]
  congr 1
  have h : (gmat (fun i => toR ((Module.Basis.span hf) i : ι → ℤ)))
      = (gmat (fun i => toR (f i))) := by
    ext i j
    simp only [gmat_apply, dotR, toR, Module.Basis.coe_span_apply]
  rw [h]

/-- `detL` of a lattice presented as the span of a linearly independent family. -/
lemma detL_eq_sqrt_gmat_of_span {κ : Type*} [Fintype κ] [DecidableEq κ] (f : κ → ι → ℤ)
    (hf : LinearIndependent ℤ f) (L : Submodule ℤ (ι → ℤ))
    (hspan : Submodule.span ℤ (Set.range f) = L) :
    detL L = Real.sqrt (gmat (fun i => toR (f i))).det :=
  hspan ▸ detL_span_gram f hf

/-! ## Diagonal scaling and shear invariance of the Gram determinant -/

/-- The shear matrix `fromBlocks 1 0 (-c) 1`. -/
def shear {κ : Type*} [Fintype κ] [DecidableEq κ] (c : κ → ℝ) :
    Matrix (κ ⊕ Fin 1) (κ ⊕ Fin 1) ℝ :=
  Matrix.fromBlocks (1 : Matrix κ κ ℝ) (0 : Matrix κ (Fin 1) ℝ)
    (Matrix.of (fun (_ : Fin 1) (a : κ) => -c a)) (1 : Matrix (Fin 1) (Fin 1) ℝ)

lemma shear_apply_inl_inl {κ : Type*} [Fintype κ] [DecidableEq κ] (c : κ → ℝ) (a b : κ) :
    shear c (Sum.inl a) (Sum.inl b) = if a = b then 1 else 0 := by
  rw [shear, Matrix.fromBlocks_apply₁₁, Matrix.one_apply]

lemma shear_apply_inl_inr {κ : Type*} [Fintype κ] [DecidableEq κ] (c : κ → ℝ) (a : κ) (b : Fin 1) :
    shear c (Sum.inl a) (Sum.inr b) = 0 := by
  rw [shear, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply]

lemma shear_apply_inr_inl {κ : Type*} [Fintype κ] [DecidableEq κ] (c : κ → ℝ) (a : Fin 1) (b : κ) :
    shear c (Sum.inr a) (Sum.inl b) = -c b := by
  rw [shear, Matrix.fromBlocks_apply₂₁, Matrix.of_apply]

lemma shear_apply_inr_inr {κ : Type*} [Fintype κ] [DecidableEq κ] (c : κ → ℝ) (a b : Fin 1) :
    shear c (Sum.inr a) (Sum.inr b) = 1 := by
  have h : a = b := Subsingleton.elim a b
  subst h
  rw [shear, Matrix.fromBlocks_apply₂₂, Matrix.one_apply_eq]

lemma det_shear {κ : Type*} [Fintype κ] [DecidableEq κ] (c : κ → ℝ) : (shear c).det = 1 := by
  rw [shear, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, Matrix.det_one, mul_one]

lemma gmat_smul_diagonal {κ : Type*} [Fintype κ] [DecidableEq κ]
    (z : κ → ι → ℝ) (d : κ → ℝ) :
    gmat (fun i => d i • z i) = Matrix.diagonal d * gmat z * Matrix.diagonal d := by
  have h := gmat_change (z := z) (z' := fun i => d i • z i) (T := Matrix.diagonal d) (by
    intro j
    funext k
    rw [show (d j • z j) k = d j * z j k by simp]
    rw [Finset.sum_eq_single j]
    · simp [Matrix.diagonal_apply_eq]
    · intro b _ hb
      simp [Matrix.diagonal_apply_ne _ hb]
    · intro h; exact absurd (Finset.mem_univ j) h)
  rw [h, Matrix.diagonal_transpose]

lemma det_gmat_smul_diagonal {κ : Type*} [Fintype κ] [DecidableEq κ]
    (z : κ → ι → ℝ) (d : κ → ℝ) :
    (gmat (fun i => d i • z i)).det = (∏ i, d i) ^ 2 * (gmat z).det := by
  rw [gmat_smul_diagonal, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
  ring

lemma gmat_shear {κ : Type*} [Fintype κ] [DecidableEq κ]
    (z : κ ⊕ Fin 1 → ι → ℝ) (c : κ → ℝ) :
    gmat (Sum.elim (fun a : κ => z (Sum.inl a) - c a • z (Sum.inr 0))
        (fun u : Fin 1 => z (Sum.inr u)))
      = (shear c).transpose * gmat z * shear c := by
  classical
  have hdet : ∀ (j : κ ⊕ Fin 1) (k : ι),
      (Sum.elim (fun a : κ => z (Sum.inl a) - c a • z (Sum.inr 0))
        (fun u : Fin 1 => z (Sum.inr u)) j) k
      = ∑ i, shear c i j * z i k := by
    intro j k
    rcases j with b | b'
    · rw [Fintype.sum_sum_type]
      have h1 : (∑ a : κ, shear c (Sum.inl a) (Sum.inl b) * z (Sum.inl a) k) = z (Sum.inl b) k := by
        rw [Finset.sum_eq_single b]
        · rw [shear_apply_inl_inl, if_pos rfl, one_mul]
        · intro a _ ha
          rw [shear_apply_inl_inl, if_neg ha, zero_mul]
        · intro h; exact absurd (Finset.mem_univ b) h
      have h2 : (∑ a' : Fin 1, shear c (Sum.inr a') (Sum.inl b) * z (Sum.inr a') k)
          = -c b * z (Sum.inr 0) k := by
        rw [Fin.sum_univ_one, shear_apply_inr_inl]
      rw [h1, h2]
      simp only [Sum.elim_inl, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      ring
    · rw [Fintype.sum_sum_type]
      have h1 : (∑ a : κ, shear c (Sum.inl a) (Sum.inr b') * z (Sum.inl a) k) = 0 := by
        simp [shear_apply_inl_inr]
      have h2 : (∑ a' : Fin 1, shear c (Sum.inr a') (Sum.inr b') * z (Sum.inr a') k)
          = z (Sum.inr b') k := by
        rw [show b' = 0 from Subsingleton.elim b' 0, Fin.sum_univ_one, shear_apply_inr_inr,
          one_mul]
      rw [h1, h2]
      simp only [Sum.elim_inr]
      ring
  exact gmat_change (z := z)
    (z' := Sum.elim (fun a : κ => z (Sum.inl a) - c a • z (Sum.inr 0))
      (fun u : Fin 1 => z (Sum.inr u))) (T := shear c)
    (by intro j; funext k; exact hdet j k)

/-! ## Covolume of the scaled projection -/

theorem detL_projScale_bound (L : Submodule ℤ (ι → ℤ)) (u : ι → ℤ) (hu : u ∈ L) (hu0 : u ≠ 0)
    (hshort : ∀ v ∈ L, v ≠ 0 → eNorm u ≤ eNorm v) (hr : 2 ≤ rk L) :
    detL (Submodule.map (projScale u) L) = (eNorm u) ^ (2 * rk L - 3) * detL L := by
  classical
  set L' : Submodule ℤ (ι → ℤ) := Submodule.map (projScale u) L with hL'def
  set ell : ℝ := eNorm u with hell
  have hellpos : 0 < ell := by rw [hell]; exact eNorm_pos_of_ne_zero hu0
  have hellne : ell ≠ 0 := ne_of_gt hellpos
  set ell2 : ℝ := ((dotZ u u : ℤ) : ℝ) with hell2
  have hell2_eq : ell2 = ell ^ 2 := by rw [hell2, ← eNorm_sq_eq u, hell]
  have hell2pos : 0 < ell2 := by rw [hell2_eq]; positivity
  have hell2ne : ell2 ≠ 0 := ne_of_gt hell2pos
  have hrkL' : rk L' = rk L - 1 := by
    rw [hL'def]; exact MDEstimates.rk_projScale L u hu hu0 hshort
  obtain ⟨n, b0⟩ := Submodule.basisOfPid (Pi.basisFun ℤ ι) L'
  have hfrL' : Module.finrank ℤ ↥L' = n := by
    rw [Module.finrank_eq_card_basis b0, Fintype.card_fin]
  have hn : n = rk L - 1 := by
    have h1 : rk L' = rk L - 1 := hrkL'
    simp only [rk] at h1 hfrL' ⊢
    omega
  let y : Module.Basis (Fin (rk L - 1)) ℤ L' := b0.reindex (finCongr hn)
  have hlift : ∀ j : Fin (rk L - 1), ∃ x ∈ L, projScale u x = ((y j : L') : ι → ℤ) := by
    intro j
    obtain ⟨x, hxL, hx⟩ := Submodule.mem_map.mp (y j).2
    exact ⟨x, hxL, hx⟩
  choose x hxL hxy using hlift
  have hy_orth : ∀ j, dotZ (((y j : L') : ι → ℤ)) u = 0 := by
    intro j
    obtain ⟨z, hzL, hz⟩ := Submodule.mem_map.mp (y j).2
    rw [← hz, dotZ_projScale_right]
  set V : Fin (rk L - 1) ⊕ Fin 1 → ι → ℤ := Sum.elim x (fun _ => u) with hVdef
  set W : Fin (rk L - 1) ⊕ Fin 1 → ι → ℤ :=
    Sum.elim (fun j => ((y j : L') : ι → ℤ)) (fun _ => u) with hWdef
  -- independence and spanning of the family `V`
  have hV_ind : LinearIndependent ℤ V := by
    rw [Fintype.linearIndependent_iff]
    intro c hc
    have h2 : (∑ i, c i • projScale u (V i)) = 0 := by
      have h3 : projScale u (∑ i, c i • V i) = ∑ i, c i • projScale u (V i) := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [map_smul]
      rw [← h3, hc, map_zero]
    have h4 : (∑ j : Fin (rk L - 1), c (Sum.inl j) • ((y j : L') : ι → ℤ)) = 0 := by
      have h5 := h2
      rw [Fintype.sum_sum_type] at h5
      simpa [hVdef, Sum.elim_inl, Sum.elim_inr, hxy, projScale_self] using h5
    have h6 : ∀ j, c (Sum.inl j) = 0 := by
      intro j
      have h7 : (∑ j, c (Sum.inl j) • y j : L') = 0 := Subtype.ext (by simpa using h4)
      exact Fintype.linearIndependent_iff.mp y.linearIndependent (fun j => c (Sum.inl j)) h7 j
    have h8 : c (Sum.inr 0) • u = 0 := by
      have h10 : (∑ j : Fin (rk L - 1), c (Sum.inl j) • x j) = 0 :=
        Finset.sum_eq_zero fun j _ => by rw [h6 j, zero_smul]
      have h9 : (∑ j : Fin (rk L - 1), c (Sum.inl j) • x j)
          + (∑ k : Fin 1, c (Sum.inr k) • u) = 0 := by
        have h := hc
        rw [hVdef, Fintype.sum_sum_type] at h
        simpa [Sum.elim_inl, Sum.elim_inr] using h
      rw [h10, zero_add, Fin.sum_univ_one] at h9
      exact h9
    intro i
    rcases i with j | k
    · exact h6 j
    · have hk : k = 0 := Subsingleton.elim k 0
      rw [hk]
      rcases smul_eq_zero.mp h8 with h | h
      · exact h
      · exact absurd h hu0
  have hV_span : Submodule.span ℤ (Set.range V) = L := by
    refine le_antisymm ?_ ?_
    · rw [Submodule.span_le]
      rintro z ⟨i, rfl⟩
      rcases i with j | k
      · exact hxL j
      · exact hu
    · intro z hz
      have hz' : projScale u z ∈ L' := Submodule.mem_map_of_mem (f := projScale u) hz
      set a : Fin (rk L - 1) → ℤ := y.equivFun ⟨projScale u z, hz'⟩ with hadef
      have hy : (∑ j, a j • ((y j : L') : ι → ℤ)) = projScale u z := by
        have h : (∑ j, a j • y j : L') = (⟨projScale u z, hz'⟩ : L') := by
          rw [← Module.Basis.equivFun_symm_apply, hadef]
          exact LinearEquiv.symm_apply_apply _ _
        simpa using congrArg (fun v : L' => (v : ι → ℤ)) h
      have hproj : projScale u (z - ∑ j, a j • x j) = 0 := by
        have h1 : projScale u (z - ∑ j, a j • x j)
            = projScale u z - ∑ j, a j • projScale u (x j) := by
          rw [map_sub, map_sum]
          congr 1
          exact Finset.sum_congr rfl fun j _ => map_smul _ _ _
        rw [h1]
        simp only [hxy]
        rw [← hy, sub_self]
      have hsubL : z - ∑ j, a j • x j ∈ L :=
        Submodule.sub_mem _ hz (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ (hxL j))
      obtain ⟨m, hm⟩ := MDEstimates.projScale_eq_zero_imp L hu hu0 (by
        intro v hv hv0
        have h := hshort v hv hv0
        rwa [hell] at h) hsubL hproj
      have hz_eq : z = (∑ j, a j • x j) + m • u := by
        rw [sub_eq_iff_eq_add] at hm
        rw [hm, add_comm]
      rw [hz_eq]
      refine Submodule.add_mem _ ?_ (Submodule.smul_mem _ _ ?_)
      · refine Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_
        exact Submodule.subset_span (by rw [hVdef]; exact Set.mem_range_self (Sum.inl j))
      · exact Submodule.subset_span (by rw [hVdef]; exact Set.mem_range_self (Sum.inr 0))
  -- Gram determinants
  have hy_ind : LinearIndependent ℤ (fun j : Fin (rk L - 1) => ((y j : L') : ι → ℤ)) :=
    y.linearIndependent.map' L'.subtype (Submodule.ker_subtype L')
  have hy_span : Submodule.span ℤ (Set.range (fun j : Fin (rk L - 1) => ((y j : L') : ι → ℤ)))
      = L' := by
    have h1 : Submodule.span ℤ (Set.range (fun j : Fin (rk L - 1) => ((y j : L') : ι → ℤ)))
        = Submodule.map L'.subtype (Submodule.span ℤ (Set.range y)) := by
      rw [Submodule.map_span]
      congr 1
      ext z
      constructor
      · rintro ⟨j, rfl⟩
        exact ⟨y j, ⟨j, rfl⟩, rfl⟩
      · rintro ⟨w, ⟨j, rfl⟩, rfl⟩
        exact ⟨j, rfl⟩
    rw [h1, Module.Basis.span_eq, Submodule.map_top]
    exact Submodule.range_subtype L'
  have hdetL' : detL L'
      = Real.sqrt (gmat (fun j : Fin (rk L - 1) => toR (((y j : L') : ι → ℤ)))).det :=
    detL_eq_sqrt_gmat_of_span _ hy_ind L' hy_span
  have hdetL : detL L = Real.sqrt (gmat (fun i => toR (V i))).det :=
    detL_eq_sqrt_gmat_of_span V hV_ind L hV_span
  -- the block structure of the Gram matrix of `W`
  have hblock : gmat (fun i => toR (W i)) =
      Matrix.fromBlocks (gmat (fun j : Fin (rk L - 1) => toR (((y j : L') : ι → ℤ))))
        (0 : Matrix (Fin (rk L - 1)) (Fin 1) ℝ)
        (0 : Matrix (Fin 1) (Fin (rk L - 1)) ℝ)
        (Matrix.of (fun _ _ : Fin 1 => ell2)) := by
    ext i j
    rcases i with a | a' <;> rcases j with b | b'
    · simp only [gmat_apply, Matrix.fromBlocks_apply₁₁, hWdef, Sum.elim_inl]
    · rw [gmat_apply, Matrix.fromBlocks_apply₁₂, Matrix.zero_apply, hWdef, ← cast_dotZ]
      simp [Sum.elim_inl, Sum.elim_inr, hy_orth]
    · simp only [gmat_apply, Matrix.fromBlocks_apply₂₁, Matrix.zero_apply, hWdef,
        Sum.elim_inl, Sum.elim_inr, ← cast_dotZ, dotZ_comm u, hy_orth, Int.cast_zero]
    · rw [gmat_apply, Matrix.fromBlocks_apply₂₂, Matrix.of_apply, hWdef, ← cast_dotZ, hell2]
      simp [Sum.elim_inr]
  have hdet_block : (gmat (fun i => toR (W i))).det
      = ell2 * (gmat (fun j : Fin (rk L - 1) => toR (((y j : L') : ι → ℤ)))).det := by
    rw [hblock, Matrix.det_fromBlocks_zero₁₂, Matrix.det_fin_one, Matrix.of_apply]
    ring
  -- the sheared and diagonally rescaled family
  set c : Fin (rk L - 1) → ℝ := fun j => dotR (toR (x j)) (toR u) / ell2 with hcdef
  set Vt : Fin (rk L - 1) ⊕ Fin 1 → ι → ℝ :=
    Sum.elim (fun j => toR (x j) - c j • toR u) (fun _ => toR u) with hVtdef
  have hW_diag : ∀ i, toR (W i)
      = (Sum.elim (fun _ : Fin (rk L - 1) => ell2) (fun _ : Fin 1 => 1) i) • Vt i := by
    intro i
    rcases i with j | k
    · rw [hWdef, Sum.elim_inl, ← hxy j, hVtdef, Sum.elim_inl, hcdef, hell2]
      exact toR_projScale u (x j) hu0
    · rw [hWdef, Sum.elim_inr, hVtdef, Sum.elim_inr]
      simp
  have hdetW2 : (gmat (fun i => toR (W i))).det
      = (ell2 ^ (rk L - 1)) ^ 2 * (gmat Vt).det := by
    have h := det_gmat_smul_diagonal (z := Vt)
      (d := Sum.elim (fun _ : Fin (rk L - 1) => ell2) (fun _ : Fin 1 => 1))
    have h2 : (fun i => Sum.elim (fun _ : Fin (rk L - 1) => ell2) (fun _ : Fin 1 => 1) i • Vt i)
        = (fun i => toR (W i)) := by
      funext i
      exact (hW_diag i).symm
    rw [h2] at h
    have h3 : (∏ i : Fin (rk L - 1) ⊕ Fin 1, Sum.elim (fun _ : Fin (rk L - 1) => ell2)
        (fun _ : Fin 1 => 1) i) = ell2 ^ (rk L - 1) := by
      rw [Fintype.prod_sum_type]
      simp
    rw [h3] at h
    exact h
  have hVtform : Vt = Sum.elim
      (fun a : Fin (rk L - 1) => toR (V (Sum.inl a)) - c a • toR (V (Sum.inr 0)))
      (fun u : Fin 1 => toR (V (Sum.inr u))) := by
    funext i
    rcases i with a | u
    · simp only [hVtdef, hVdef, Sum.elim_inl, Sum.elim_inr]
    · simp only [hVtdef, hVdef, Sum.elim_inr]
  have hdetVt : (gmat Vt).det = (gmat (fun i => toR (V i))).det := by
    have hs : gmat (Sum.elim
        (fun a : Fin (rk L - 1) => toR (V (Sum.inl a)) - c a • toR (V (Sum.inr 0)))
        (fun u : Fin 1 => toR (V (Sum.inr u))))
        = (shear c).transpose * gmat (fun i => toR (V i)) * shear c :=
      gmat_shear (z := fun i => toR (V i)) (c := c)
    rw [hVtform, hs, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, det_shear]
    ring
  have hfinal : (gmat (fun j : Fin (rk L - 1) => toR (((y j : L') : ι → ℤ)))).det
      = ell2 ^ (2 * (rk L - 1) - 1) * (gmat (fun i => toR (V i))).det := by
    have h1 : ell2 * (gmat (fun j : Fin (rk L - 1) => toR (((y j : L') : ι → ℤ)))).det
        = (ell2 ^ (rk L - 1)) ^ 2 * (gmat (fun i => toR (V i))).det := by
      rw [← hdet_block, hdetW2, hdetVt]
    have h3 : ell2 ^ (2 * (rk L - 1) - 1) * ell2 = (ell2 ^ (rk L - 1)) ^ 2 := by
      rw [← pow_succ, ← pow_mul]
      congr 1
      omega
    calc (gmat (fun j : Fin (rk L - 1) => toR (((y j : L') : ι → ℤ)))).det
        = ell2 * (gmat (fun j : Fin (rk L - 1) => toR (((y j : L') : ι → ℤ)))).det / ell2 := by
          field_simp
      _ = (ell2 ^ (rk L - 1)) ^ 2 * (gmat (fun i => toR (V i))).det / ell2 := by rw [h1]
      _ = ell2 ^ (2 * (rk L - 1) - 1) * (gmat (fun i => toR (V i))).det := by
          rw [← h3]; field_simp
  have h4 : ell2 ^ (2 * (rk L - 1) - 1) = (ell ^ (2 * rk L - 3)) ^ 2 := by
    rw [hell2_eq, ← pow_mul, ← pow_mul]
    congr 1
    omega
  calc detL L'
      = Real.sqrt (gmat (fun j : Fin (rk L - 1) => toR (((y j : L') : ι → ℤ)))).det := hdetL'
    _ = Real.sqrt (ell2 ^ (2 * (rk L - 1) - 1) * (gmat (fun i => toR (V i))).det) := by
          rw [hfinal]
    _ = Real.sqrt (ell2 ^ (2 * (rk L - 1) - 1))
          * Real.sqrt (gmat (fun i => toR (V i))).det :=
          Real.sqrt_mul (by positivity) _
    _ = ell ^ (2 * rk L - 3) * detL L := by
          rw [hdetL, h4, Real.sqrt_sq (by positivity)]

/-! ## The successive minima of the scaled projection -/

theorem lam_projScale_bound (L : Submodule ℤ (ι → ℤ)) (u : ι → ℤ) (hu : u ∈ L) (hu0 : u ≠ 0)
    (hshort : ∀ v ∈ L, v ≠ 0 → eNorm u ≤ eNorm v) (j : ℕ) (hj : 1 ≤ j) (hjR : j ≤ rk L - 1) :
    lam L (j + 1) ≤ 2 / Real.sqrt 3 * lam (Submodule.map (projScale u) L) j / (eNorm u) ^ 2 := by
  classical
  set L' : Submodule ℤ (ι → ℤ) := Submodule.map (projScale u) L with hL'def
  set ell : ℝ := eNorm u with hell
  have hellpos : 0 < ell := by rw [hell]; exact eNorm_pos_of_ne_zero hu0
  have hrkL' : rk L' = rk L - 1 := by
    rw [hL'def]; exact MDEstimates.rk_projScale L u hu hu0 hshort
  have hjR' : j ≤ rk L' := by rw [hrkL']; omega
  have hshort' : ∀ v ∈ L, v ≠ 0 → eNorm u ≤ eNorm v := hshort
  -- (1) `lam L' 1 ≥ (√3/2) ‖u‖³`
  have hone : Real.sqrt 3 / 2 * ell ^ 3 ≤ lam L' 1 := by
    rw [lam_eq_sInf]
    refine le_csInf (lamSet_nonempty L' (by rw [hrkL']; omega)) ?_
    rintro r ⟨hr0, f, hfL', hfLI, hfr⟩
    have hf0 : f 0 ≠ 0 := hfLI.ne_zero 0
    obtain ⟨x, hxL, hxx, hxbd⟩ := MDEstimates.exists_lift_norm L u hu hu0 (hfL' 0)
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [map_zero] at hxx
      exact hf0 hxx.symm
    have hxl : ell ≤ eNorm x := by
      have h := hshort' x hxL hx0
      rwa [hell]
    have h1 : ell ^ 2 ≤ eNorm x ^ 2 := by nlinarith [eNorm_nonneg x]
    have h2 : (3 / 4) * ell ^ 2 ≤ eNorm (f 0) ^ 2 / ell ^ 4 := by linarith
    have h5 : (3 / 4) * ell ^ 6 ≤ eNorm (f 0) ^ 2 := by
      have hell4 : 0 < ell ^ 4 := by positivity
      have h6 := (le_div_iff₀ hell4).mp h2
      nlinarith [h6]
    have h6 : Real.sqrt ((3 : ℝ) / 4 * ell ^ 6) ≤ eNorm (f 0) := by
      have h7 := Real.sqrt_le_sqrt h5
      rwa [Real.sqrt_sq (eNorm_nonneg _)] at h7
    have h7 : Real.sqrt ((3 : ℝ) / 4 * ell ^ 6) = Real.sqrt 3 / 2 * ell ^ 3 := by
      rw [show (3 : ℝ) / 4 * ell ^ 6 = (Real.sqrt 3 / 2 * ell ^ 3) ^ 2 by
        rw [mul_pow, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]; ring]
      rw [Real.sqrt_sq]; positivity
    rw [h7] at h6
    exact h6.trans (hfr 0)
  -- (2) the recursion
  have hmain : ∀ ρ : ℝ, lam L' j < ρ → lam L (j + 1) ≤ 2 / Real.sqrt 3 * ρ / ell ^ 2 := by
    intro ρ hρ
    obtain ⟨s, ⟨hs0, f, hfL', hfLI, hfs⟩, hsρ⟩ :=
      exists_lt_of_csInf_lt (lamSet_nonempty L' hjR')
        (by rw [lam_eq_sInf] at hρ; exact hρ)
    have hfρ : ∀ t, eNorm (f t) ≤ ρ := fun t => (hfs t).trans hsρ.le
    choose g hgL hgψ hgbd using fun t => MDEstimates.exists_lift_norm L u hu hu0 (hfL' t)
    have hρ' : lam L' j < ρ := by
      rw [lam_eq_sInf]
      exact lt_of_le_of_lt (csInf_le (bddBelow_lamSet L' j) ⟨hs0, f, hfL', hfLI, hfs⟩) hsρ
    have hlamlow : Real.sqrt 3 / 2 * ell ^ 3 ≤ lam L' j :=
      hone.trans (lam_mono L' (by omega) hjR')
    have hlow : Real.sqrt 3 / 2 * ell ^ 3 ≤ ρ := hlamlow.trans hρ'.le
    have hρpos : 0 < ρ := lt_of_lt_of_le (by positivity) hlow
    have hgt : ∀ t : Fin j, eNorm (g t) ≤ 2 / Real.sqrt 3 * ρ / ell ^ 2 := by
      intro t
      have hsq : eNorm (g t) ^ 2 ≤ (4 / 3) * ρ ^ 2 / ell ^ 4 := by
        have h2 : eNorm (f t) ^ 2 ≤ ρ ^ 2 := by
          have := hfρ t
          nlinarith [eNorm_nonneg (f t)]
        have h3 : ell ^ 2 / 4 ≤ ρ ^ 2 / (3 * ell ^ 4) := by
          have ha : (0 : ℝ) ≤ Real.sqrt 3 / 2 * ell ^ 3 := by positivity
          have h4 : (Real.sqrt 3 / 2 * ell ^ 3) ^ 2 ≤ ρ ^ 2 := by
            nlinarith [hlow, ha, hρpos.le]
          have h5 : (Real.sqrt 3 / 2 * ell ^ 3) ^ 2 = (3 / 4) * ell ^ 6 := by
            rw [mul_pow, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]; ring
          rw [h5] at h4
          rw [le_div_iff₀ (by positivity : (0 : ℝ) < 3 * ell ^ 4)]
          nlinarith [h4]
        calc eNorm (g t) ^ 2 ≤ eNorm (f t) ^ 2 / ell ^ 4 + ell ^ 2 / 4 := hgbd t
          _ ≤ ρ ^ 2 / ell ^ 4 + ρ ^ 2 / (3 * ell ^ 4) :=
              add_le_add (div_le_div_of_nonneg_right h2 (by positivity)) h3
          _ = (4 / 3) * ρ ^ 2 / ell ^ 4 := by ring
      have h7 : ((2 : ℝ) / Real.sqrt 3 * ρ / ell ^ 2) ^ 2 = (4 / 3) * ρ ^ 2 / ell ^ 4 := by
        rw [div_pow, mul_pow, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
        ring
      have h8 := Real.sqrt_le_sqrt hsq
      rw [Real.sqrt_sq (eNorm_nonneg (g t)), ← h7,
        Real.sqrt_sq (by positivity)] at h8
      exact h8
    have huM : eNorm u ≤ 2 / Real.sqrt 3 * ρ / ell ^ 2 := by
      have h3 : Real.sqrt 3 * ell ^ 3 ≤ 2 * ρ := by nlinarith [hlow]
      have h4 : ell ^ 3 ≤ 2 * ρ / Real.sqrt 3 := by
        rw [le_div_iff₀ (Real.sqrt_pos_of_pos (by norm_num : (0 : ℝ) < 3))]
        nlinarith [h3]
      have h5 : ell ≤ 2 * ρ / Real.sqrt 3 / ell ^ 2 := by
        rw [le_div_iff₀ (by positivity : (0 : ℝ) < ell ^ 2)]
        calc ell * ell ^ 2 = ell ^ 3 := by ring
          _ ≤ 2 * ρ / Real.sqrt 3 := h4
      rw [hell] at h5
      have h6 : (2 : ℝ) * ρ / Real.sqrt 3 / (eNorm u) ^ 2
          = 2 / Real.sqrt 3 * ρ / (eNorm u) ^ 2 := by ring
      simpa [h6] using h5
    set F : Fin (j + 1) → ι → ℤ := Fin.cases u g with hFdef
    have hF_ind : LinearIndependent ℤ F := by
      rw [Fintype.linearIndependent_iff]
      intro c hc
      have h2 : projScale u (∑ i, c i • F i) = ∑ i, c i • projScale u (F i) := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [map_smul]
      have h3 : (∑ i : Fin (j + 1), c i • projScale u (F i)) = 0 := by
        rw [← h2, hc, map_zero]
      rw [Fin.sum_univ_succ] at h3
      have h4 : (∑ i : Fin j, c i.succ • f i) = 0 := by
        simpa [hFdef, Fin.cases_zero, Fin.cases_succ, hgψ, projScale_self] using h3
      have h5 : ∀ i : Fin j, c i.succ = 0 :=
        Fintype.linearIndependent_iff.mp hfLI (fun i => c i.succ) h4
      have h6 : c 0 • u = 0 := by
        have h7 := hc
        rw [Fin.sum_univ_succ] at h7
        have h8 : (∑ i : Fin j, c i.succ • F i.succ) = 0 := by
          refine Finset.sum_eq_zero fun i _ => ?_
          rw [h5 i, zero_smul]
        rw [h8, add_zero] at h7
        simpa [hFdef, Fin.cases_zero] using h7
      intro i
      rcases Fin.eq_zero_or_eq_succ i with h | ⟨k, rfl⟩
      · rw [h]
        rcases smul_eq_zero.mp h6 with hh | hh
        · exact hh
        · exact absurd hh hu0
      · exact h5 k
    rw [lam_eq_sInf]
    refine csInf_le (bddBelow_lamSet L (j + 1)) ?_
    refine ⟨by positivity, F, ?_, hF_ind, ?_⟩
    · intro i
      rcases Fin.eq_zero_or_eq_succ i with h | ⟨k, rfl⟩
      · rw [h]; simpa [hFdef] using hu
      · simpa [hFdef] using hgL k
    · intro i
      rcases Fin.eq_zero_or_eq_succ i with h | ⟨k, rfl⟩
      · rw [h]; simpa [hFdef] using huM
      · simpa [hFdef] using hgt k
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hεpos : 0 < ε * (Real.sqrt 3 / 2 * ell ^ 2) := mul_pos hε (by positivity)
  have h := hmain (lam L' j + ε * (Real.sqrt 3 / 2 * ell ^ 2))
    (lt_add_of_pos_right _ hεpos)
  calc lam L (j + 1)
      ≤ 2 / Real.sqrt 3 * (lam L' j + ε * (Real.sqrt 3 / 2 * ell ^ 2)) / ell ^ 2 := h
    _ = 2 / Real.sqrt 3 * lam L' j / ell ^ 2 + ε := by
        field_simp

/-! ## Minkowski's second theorem (upper bound) -/

lemma detL_bot : detL (⊥ : Submodule ℤ (ι → ℤ)) = 1 := by
  have hf : LinearIndependent ℤ (fun i : Fin 0 => (0 : ι → ℤ)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    exact i.elim0
  have hspan : Submodule.span ℤ (Set.range (fun i : Fin 0 => (0 : ι → ℤ))) = ⊥ := by
    rw [show Set.range (fun i : Fin 0 => (0 : ι → ℤ)) = ∅ by ext x; simp]
    exact Submodule.span_empty
  rw [← hspan, detL_span_gram _ hf]
  simp [gmat, Matrix.det_fin_zero]

lemma minkowski_base (L : Submodule ℤ (ι → ℤ)) (h : rk L ≤ 1) :
    (∏ j ∈ Finset.range (rk L), lam L (j + 1)) ≤ detL L := by
  rcases Nat.eq_zero_or_pos (rk L) with h0 | h1
  · have hbot : L = ⊥ := Submodule.finrank_eq_zero.mp (by rw [← rk]; exact h0)
    rw [h0]
    rw [hbot, detL_bot]
    simp
  · have h1' : rk L = 1 := le_antisymm h h1
    rw [h1']
    simp only [Finset.range_one, Finset.prod_singleton, Nat.zero_add]
    obtain ⟨n, b0⟩ := Submodule.basisOfPid (Pi.basisFun ℤ ι) L
    have hn : n = 1 := by
      have h := Module.finrank_eq_card_basis b0
      rw [Fintype.card_fin] at h
      rw [← h, ← rk, h1']
    subst hn
    have hdet : detL L = eNorm ((b0 0 : L) : ι → ℤ) := by
      rw [detL_eq_sqrt_gmat b0, Matrix.det_fin_one, gmat_apply, ← cast_dotZ, ← eNorm_sq_eq]
      exact Real.sqrt_sq (eNorm_nonneg _)
    rw [hdet]
    exact lam_one_le_eNorm L (b0 0).2 (fun h => b0.ne_zero 0 (Subtype.ext h))

theorem minkowski_upper (ι : Type) [Fintype ι] [DecidableEq ι] :
    ∃ K : ℝ, 0 < K ∧ ∀ (L : Submodule ℤ (ι → ℤ)),
      (∏ j ∈ Finset.range (rk L), lam L (j + 1)) ≤ K * detL L := by
  classical
  set C : ℝ := 2 / Real.sqrt 3 with hCdef
  have hCpos : 0 < C := by rw [hCdef]; positivity
  have hC1 : 1 ≤ C := by
    rw [hCdef, le_div_iff₀ (Real.sqrt_pos_of_pos (by norm_num : (0 : ℝ) < 3))]
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3), Real.sqrt_nonneg 3]
  refine ⟨C ^ (Fintype.card ι * Fintype.card ι), by positivity, ?_⟩
  intro L
  have hrkbot : rk (⊥ : Submodule ℤ (ι → ℤ)) = 0 := by
    rw [rk]; exact Submodule.finrank_eq_zero.mpr rfl
  have hcard : rk L ≤ Fintype.card ι := by
    rw [rk]
    refine (Submodule.finrank_le L).trans ?_
    rw [Module.finrank_fintype_fun_eq_card]
  have key : ∀ r : ℕ, ∀ L : Submodule ℤ (ι → ℤ), rk L ≤ r →
      (∏ j ∈ Finset.range (rk L), lam L (j + 1)) ≤ C ^ (rk L * rk L) * detL L := by
    intro r
    induction r using Nat.strong_induction_on with
    | _ r ih =>
      intro L hL
      rcases Nat.lt_or_ge (rk L) 2 with h2 | h2
      · have hb := minkowski_base L (by omega)
        calc (∏ j ∈ Finset.range (rk L), lam L (j + 1)) ≤ detL L := hb
          _ ≤ C ^ (rk L * rk L) * detL L := by
              have h1 : (1 : ℝ) ≤ C ^ (rk L * rk L) := one_le_pow₀ hC1
              nlinarith [detL_nonneg L]
      · have hne : L ≠ ⊥ := by
          rintro rfl
          rw [hrkbot] at h2
          omega
        obtain ⟨b, hbL, hb0, hbmin⟩ := BCS.shortest_vec L hne
        have hbn : eNorm b = lam L 1 := by
          refine le_antisymm ?_ (lam_one_le_eNorm L hbL hb0)
          rw [lam_eq_sInf]
          refine le_csInf (lamSet_nonempty L (by omega)) ?_
          rintro r ⟨hr0, f, hfL, hfLI, hfr⟩
          exact (hbmin (f 0) (hfL 0) (hfLI.ne_zero 0)).trans (hfr 0)
        set L' : Submodule ℤ (ι → ℤ) := Submodule.map (projScale b) L with hL'def
        have hrkL' : rk L' = rk L - 1 := by
          rw [hL'def]; exact MDEstimates.rk_projScale L b hbL hb0 hbmin
        have hdet : detL L' = (eNorm b) ^ (2 * rk L - 3) * detL L :=
          detL_projScale_bound L b hbL hb0 hbmin (by omega)
        have hIH : (∏ j ∈ Finset.range (rk L'), lam L' (j + 1))
            ≤ C ^ (rk L' * rk L') * detL L' := ih (rk L') (by omega) L' le_rfl
        rw [hrkL'] at hIH
        have hsplit : (∏ j ∈ Finset.range (rk L), lam L (j + 1))
            = eNorm b * ∏ j ∈ Finset.range (rk L - 1), lam L (j + 2) := by
          have hsucc : rk L - 1 + 1 = rk L := by omega
          have h1 : (∏ j ∈ Finset.range (rk L), lam L (j + 1))
              = (∏ j ∈ Finset.range (rk L - 1), lam L (j + 2)) * lam L 1 := by
            conv_lhs => rw [← hsucc, Finset.prod_range_succ']
          rw [h1, ← hbn, mul_comm]
        have hfac : ∀ t ∈ Finset.range (rk L - 1),
            lam L (t + 2) ≤ C * lam L' (t + 1) / (eNorm b) ^ 2 := by
          intro t ht
          have ht' : t + 2 ≤ rk L := by simp at ht; omega
          have h := lam_projScale_bound L b hbL hb0 hbmin (j := t + 1) (by omega) (by omega)
          rw [hCdef]
          simpa using h
        have hprod2 : (∏ t ∈ Finset.range (rk L - 1), lam L (t + 2))
            ≤ ∏ t ∈ Finset.range (rk L - 1), (C * lam L' (t + 1) / (eNorm b) ^ 2) :=
          Finset.prod_le_prod₀ (fun t _ => lam_nonneg L (t + 2)) hfac
        have hprod3 : (∏ t ∈ Finset.range (rk L - 1), (C * lam L' (t + 1) / (eNorm b) ^ 2))
            = C ^ (rk L - 1) * (∏ t ∈ Finset.range (rk L - 1), lam L' (t + 1))
              / (eNorm b) ^ (2 * (rk L - 1)) := by
          rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_const, Finset.prod_const,
            ← pow_mul]
          simp only [Finset.card_range]
        have hbpos : 0 < eNorm b := eNorm_pos_of_ne_zero hb0
        have hQ : (∏ t ∈ Finset.range (rk L - 1), lam L' (t + 1))
            ≤ C ^ ((rk L - 1) * (rk L - 1)) * (eNorm b ^ (2 * rk L - 3) * detL L) := by
          rw [← hdet]; exact hIH
        have hstep1 : eNorm b * (C ^ (rk L - 1) *
              (∏ t ∈ Finset.range (rk L - 1), lam L' (t + 1)) / (eNorm b) ^ (2 * (rk L - 1)))
            ≤ eNorm b * (C ^ (rk L - 1) * (C ^ ((rk L - 1) * (rk L - 1)) *
                (eNorm b ^ (2 * rk L - 3) * detL L)) / (eNorm b) ^ (2 * (rk L - 1))) := by
          apply mul_le_mul_of_nonneg_left _ (le_of_lt hbpos)
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_left hQ (by positivity)
        have hEq : eNorm b * (C ^ (rk L - 1) * (C ^ ((rk L - 1) * (rk L - 1)) *
                (eNorm b ^ (2 * rk L - 3) * detL L)) / (eNorm b) ^ (2 * (rk L - 1)))
            = C ^ ((rk L - 1) + (rk L - 1) * (rk L - 1)) * detL L := by
          have hbne : eNorm b ≠ 0 := ne_of_gt hbpos
          have hkey1 : eNorm b * eNorm b ^ (2 * rk L - 3) = eNorm b ^ (2 * (rk L - 1)) := by
            rw [← pow_succ']; congr 1; omega
          repeat rw [← mul_div_assoc]
          rw [div_eq_iff (pow_ne_zero _ hbne)]
          rw [← mul_assoc (C ^ (rk L - 1)) (C ^ ((rk L - 1) * (rk L - 1))), ← pow_add]
          linear_combination (C ^ ((rk L - 1) + (rk L - 1) * (rk L - 1)) * detL L) * hkey1
        have hexp : (rk L - 1) + (rk L - 1) * (rk L - 1) ≤ rk L * rk L := by
          nlinarith [Nat.sub_add_cancel (show 1 ≤ rk L by omega)]
        calc (∏ j ∈ Finset.range (rk L), lam L (j + 1))
            = eNorm b * ∏ t ∈ Finset.range (rk L - 1), lam L (t + 2) := hsplit
          _ ≤ eNorm b * ∏ t ∈ Finset.range (rk L - 1),
                (C * lam L' (t + 1) / (eNorm b) ^ 2) :=
              mul_le_mul_of_nonneg_left hprod2 (le_of_lt hbpos)
          _ = eNorm b * (C ^ (rk L - 1) * (∏ t ∈ Finset.range (rk L - 1), lam L' (t + 1))
                  / (eNorm b) ^ (2 * (rk L - 1))) := by rw [hprod3]
          _ ≤ C ^ ((rk L - 1) + (rk L - 1) * (rk L - 1)) * detL L :=
              hstep1.trans (le_of_eq hEq)
          _ ≤ C ^ (rk L * rk L) * detL L :=
              mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hC1 hexp) (detL_nonneg L)
  have hle := key (Fintype.card ι) L hcard
  refine le_trans hle ?_
  have hle2 : C ^ (rk L * rk L) ≤ C ^ (Fintype.card ι * Fintype.card ι) :=
    pow_le_pow_right₀ hC1 (Nat.mul_le_mul hcard hcard)
  exact mul_le_mul_of_nonneg_right hle2 (detL_nonneg L)

end Work.HP
