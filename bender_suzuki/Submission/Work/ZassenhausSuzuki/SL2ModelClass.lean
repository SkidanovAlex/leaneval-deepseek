import Mathlib
import Submission.Work.Models.PSL2.Defs
import Submission.Work.Models.PSL2.pslEquiv
import Submission.Work.Models.PSL2.D_facts
import Submission.Work.ZassenhausSuzuki.SingerModelDefs
import Submission.Work.ZassenhausSuzuki.SingerModelCycle.singer_cycle_model
import Submission.Work.Models.Port.Commons.LinearAlgebra.Matrix.card_SL2_field

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The conjugacy classes of `SL(2, F)`, `F` a finite field of characteristic two

This file collects the model-theoretic input of
`Work.ZassenhausSuzuki.strongly_real_conj_structure`:

* `sl2_trace_zero_sq_eq_one` — trace `0` forces `A * A = 1`;
* `sl2_conj_companion` — every element of non-zero trace is conjugate to the companion matrix
  `qalphaMat (trace A)` of its characteristic polynomial;
* `sl2_conj_of_trace_eq` — two elements with the same non-zero trace are conjugate;
* `sl2_classify` — every element has trace `0`, is conjugate into the split torus `D`, or is
  conjugate into a Singer cycle (a cyclic subgroup of order `|F| + 1`);
* `sl2_cyclic_conj_card_sub_one`, `sl2_cyclic_conj_card_add_one` — all cyclic subgroups of
  order `|F| - 1` (resp. `|F| + 1`) are conjugate.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open Matrix

namespace Work.ZassenhausSuzuki

/-- In `SL(2,F)` over a field of characteristic `2`, a matrix of trace `0` satisfies
`A * A = 1`: its characteristic polynomial is `X ^ 2 + trace A * X + det A = X ^ 2 + 1`. -/
theorem sl2_trace_zero_sq_eq_one {F : Type*} [Field F] [CharP F 2]
    (A : Matrix.SpecialLinearGroup (Fin 2) F)
    (h : (A : Matrix (Fin 2) (Fin 2) F).trace = 0) : A * A = 1 := by
  have key : (A : Matrix (Fin 2) (Fin 2) F) * (A : Matrix (Fin 2) (Fin 2) F) = 1 := by
    have hcp : (A : Matrix (Fin 2) (Fin 2) F).charpoly = Polynomial.X ^ 2 + 1 := by
      rw [Matrix.charpoly_fin_two, h, A.2]
      simp
    have hCH := Matrix.aeval_self_charpoly (A : Matrix (Fin 2) (Fin 2) F)
    rw [hcp] at hCH
    simp only [map_add, map_pow, Polynomial.aeval_X, map_one] at hCH
    have h2 : ((A : Matrix (Fin 2) (Fin 2) F)) ^ 2 = 1 := by
      have h3 : ((A : Matrix (Fin 2) (Fin 2) F)) ^ 2 = -1 := eq_neg_of_add_eq_zero_left hCH
      rwa [CharTwo.neg_eq] at h3
    rwa [pow_two] at h2
  exact Subtype.ext key

/-- The `(0,1)` entry computation behind the companion-matrix normal form. -/
private lemma companion_aux01 {F : Type*} [Field F] [CharP F 2]
    (a b c d v0 v1 t : F) (hdet : a * d + b * c = 1) (htr : a + d = t) :
    a * (a * v0 + b * v1) + b * (c * v0 + d * v1) = v0 + t * (a * v0 + b * v1) := by
  have h1 : b * c = 1 + a * d := by
    rw [← hdet]; ring_nf; rw [CharTwo.two_eq_zero]; simp
  have he : a * a + b * c = 1 + a * (a + d) := by rw [h1]; ring
  have hbd : a * b + b * d = b * (a + d) := by ring
  calc a * (a * v0 + b * v1) + b * (c * v0 + d * v1)
      = (a * a + b * c) * v0 + (a * b + b * d) * v1 := by ring
    _ = (1 + a * (a + d)) * v0 + b * (a + d) * v1 := by rw [he, hbd]
    _ = v0 + t * (a * v0 + b * v1) := by rw [htr]; ring

/-- The `(1,1)` entry computation behind the companion-matrix normal form. -/
private lemma companion_aux11 {F : Type*} [Field F] [CharP F 2]
    (a b c d v0 v1 t : F) (hdet : a * d + b * c = 1) (htr : a + d = t) :
    c * (a * v0 + b * v1) + d * (c * v0 + d * v1) = v1 + t * (c * v0 + d * v1) := by
  have h1 : b * c = 1 + a * d := by
    rw [← hdet]; ring_nf; rw [CharTwo.two_eq_zero]; simp
  have hca : c * a + d * c = c * t := by rw [← htr]; ring
  have hcb : c * b + d * d = 1 + d * (a + d) := by rw [mul_comm c b, h1]; ring
  calc c * (a * v0 + b * v1) + d * (c * v0 + d * v1)
      = (c * a + d * c) * v0 + (c * b + d * d) * v1 := by ring
    _ = c * t * v0 + (1 + d * (a + d)) * v1 := by rw [hca, hcb]
    _ = v1 + t * (c * v0 + d * v1) := by rw [htr]; ring

/-- **Every element of `SL(2,F)` with non-zero trace is conjugate to the companion matrix
`qalphaMat (trace A)`.** -/
theorem sl2_conj_companion {F : Type*} [Field F] [Finite F] [CharP F 2]
    (X : Matrix.SpecialLinearGroup (Fin 2) F)
    (hXtr : (X : Matrix (Fin 2) (Fin 2) F).trace ≠ 0) :
    ∃ h : Matrix.SpecialLinearGroup (Fin 2) F,
      h * X * h⁻¹ =
        (⟨qalphaMat (X : Matrix (Fin 2) (Fin 2) F).trace, by rw [qalphaMat_det]⟩ :
          Matrix.SpecialLinearGroup (Fin 2) F) := by
  set a : F := (X : Matrix (Fin 2) (Fin 2) F) 0 0 with ha
  set b : F := (X : Matrix (Fin 2) (Fin 2) F) 0 1 with hb
  set c : F := (X : Matrix (Fin 2) (Fin 2) F) 1 0 with hc
  set d : F := (X : Matrix (Fin 2) (Fin 2) F) 1 1 with hd
  set t : F := (X : Matrix (Fin 2) (Fin 2) F).trace with ht
  have hX : (X : Matrix (Fin 2) (Fin 2) F) = !![a, b; c, d] :=
    Matrix.eta_fin_two (X : Matrix (Fin 2) (Fin 2) F)
  have htr' : a + d = t := by
    simp only [ht, Matrix.trace_fin_two, ← ha, ← hd]
  have htne : t ≠ 0 := hXtr
  have hdet : a * d + b * c = 1 := by
    have h := X.2
    rw [Matrix.det_fin_two, sub_eq_add_neg, CharTwo.neg_eq] at h
    rw [ha, hb, hc, hd]
    exact h
  -- a cyclic vector among `(1,0)`, `(0,1)`, `(1,1)`
  obtain ⟨v0, v1, hv⟩ : ∃ v0 v1 : F, v0 * (c * v0 + d * v1) + (a * v0 + b * v1) * v1 ≠ 0 := by
    by_cases hc0 : c = 0
    · by_cases hb0 : b = 0
      · refine ⟨1, 1, ?_⟩
        intro hcon
        apply htne
        rw [← htr']
        simpa [hc0, hb0, add_comm a d] using hcon
      · refine ⟨0, 1, ?_⟩
        simpa [hc0] using hb0
    · refine ⟨1, 0, ?_⟩
      simpa using hc0
  let h0 : Matrix (Fin 2) (Fin 2) F := !![v0, a * v0 + b * v1; v1, c * v0 + d * v1]
  have h0det : h0.det ≠ 0 := by
    simp only [h0, Matrix.det_fin_two_of, sub_eq_add_neg, CharTwo.neg_eq]
    exact hv
  have h0mat : (X : Matrix (Fin 2) (Fin 2) F) * h0 = h0 * qalphaMat t := by
    rw [hX]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_two, h0, qalphaMat, Matrix.of_apply] <;>
      simp
    · simpa [mul_comm] using companion_aux01 a b c d v0 v1 t hdet htr'
    · simpa [mul_comm] using companion_aux11 a b c d v0 v1 t hdet htr'
  obtain ⟨s, hs⟩ := isSquare_of_charTwo' (h0.det)⁻¹
  have hs' : s * s = (h0.det)⁻¹ := hs.symm
  have hHdet : (s • h0).det = 1 := by
    rw [Matrix.det_smul]
    simp only [Fintype.card_fin, pow_two]
    rw [hs']
    exact inv_mul_cancel₀ h0det
  let H : Matrix.SpecialLinearGroup (Fin 2) F := ⟨s • h0, hHdet⟩
  let C : Matrix.SpecialLinearGroup (Fin 2) F := ⟨qalphaMat t, by rw [qalphaMat_det]⟩
  have hmat : X * H = H * C := by
    apply Subtype.ext
    show (X : Matrix (Fin 2) (Fin 2) F) * (s • h0) = (s • h0) * qalphaMat t
    rw [Matrix.mul_smul, Matrix.smul_mul, h0mat]
  have hconj : H⁻¹ * X * H = C := by
    calc H⁻¹ * X * H = H⁻¹ * (X * H) := by rw [mul_assoc]
      _ = H⁻¹ * (H * C) := by rw [hmat]
      _ = (H⁻¹ * H) * C := by rw [mul_assoc]
      _ = C := by rw [inv_mul_cancel, one_mul]
  have hCX : C = (⟨qalphaMat (X : Matrix (Fin 2) (Fin 2) F).trace, by rw [qalphaMat_det]⟩ :
      Matrix.SpecialLinearGroup (Fin 2) F) := by
    apply Subtype.ext
    show qalphaMat t = qalphaMat (X : Matrix (Fin 2) (Fin 2) F).trace
    rw [ht]
  exact ⟨H⁻¹, hCX ▸ (by simpa using hconj)⟩

/-- Two elements of `SL(2,F)`, `F` a finite field of characteristic `2`, with the same non-zero
trace are conjugate. -/
theorem sl2_conj_of_trace_eq {F : Type*} [Field F] [Finite F] [CharP F 2]
    {A B : Matrix.SpecialLinearGroup (Fin 2) F}
    (htr : (A : Matrix (Fin 2) (Fin 2) F).trace = (B : Matrix (Fin 2) (Fin 2) F).trace)
    (hne : (A : Matrix (Fin 2) (Fin 2) F).trace ≠ 0) :
    ∃ h : Matrix.SpecialLinearGroup (Fin 2) F, h * A * h⁻¹ = B := by
  obtain ⟨hA, hhA⟩ := sl2_conj_companion A hne
  obtain ⟨hB, hhB⟩ := sl2_conj_companion B (by rw [← htr]; exact hne)
  let CA : Matrix.SpecialLinearGroup (Fin 2) F :=
    ⟨qalphaMat (A : Matrix (Fin 2) (Fin 2) F).trace, by rw [qalphaMat_det]⟩
  let CB : Matrix.SpecialLinearGroup (Fin 2) F :=
    ⟨qalphaMat (B : Matrix (Fin 2) (Fin 2) F).trace, by rw [qalphaMat_det]⟩
  have hhA' : hA * A * hA⁻¹ = CA := by simpa only [CA] using hhA
  have hhB' : hB * B * hB⁻¹ = CB := by simpa only [CB] using hhB
  have hC : CA = CB := by
    apply Subtype.ext
    show qalphaMat (A : Matrix (Fin 2) (Fin 2) F).trace
      = qalphaMat (B : Matrix (Fin 2) (Fin 2) F).trace
    rw [htr]
  have e1 : A = hA⁻¹ * CA * hA := by rw [← hhA']; group
  have e2 : B = hB⁻¹ * CB * hB := by rw [← hhB']; group
  refine ⟨hB⁻¹ * hA, ?_⟩
  rw [e1, e2, hC]
  group

/-- **Classification of the elements of `SL(2,F)`** (`F` a finite field of characteristic `2`):
relative to the standard split torus `D` and the Singer cycles, every element either has
trace `0`, or is conjugate into `D`, or is conjugate into a cyclic subgroup of order
`Nat.card F + 1`. -/
theorem sl2_classify {F : Type*} [Field F] [Finite F] [CharP F 2]
    (A : Matrix.SpecialLinearGroup (Fin 2) F) :
    (A : Matrix (Fin 2) (Fin 2) F).trace = 0 ∨
      (∃ h : Matrix.SpecialLinearGroup (Fin 2) F,
        h * A * h⁻¹ ∈ Work.Models.PSL2.D (F := F)) ∨
      (∃ W : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F), IsCyclic ↥W ∧
        Nat.card ↥W = Nat.card F + 1 ∧
        ∃ h : Matrix.SpecialLinearGroup (Fin 2) F, h * A * h⁻¹ ∈ W) := by
  set t : F := (A : Matrix (Fin 2) (Fin 2) F).trace with ht
  by_cases htr : t = 0
  · exact Or.inl htr
  right
  by_cases hroot : ∃ z : F, z * z + t * z + 1 = 0
  · -- `X ^ 2 + t * X + 1` splits: `A` is conjugate into the split torus
    left
    obtain ⟨z, hz⟩ := hroot
    have h2 : z * z + t * z = 1 := CharTwo.add_eq_zero.mp hz
    have hmul : z * (z + t) = 1 := by
      calc z * (z + t) = z * z + t * z := by ring
        _ = 1 := h2
    have hzinv : z⁻¹ = z + t := inv_eq_of_mul_eq_one_right hmul
    have htrz : z + z⁻¹ = t := by
      rw [hzinv, ← add_assoc, CharTwo.add_self_eq_zero, zero_add]
    have hz0 : z ≠ 0 := by
      intro h0
      have h2' : (1 : F) = 0 := by rw [← h2, h0]; ring
      exact one_ne_zero h2'
    have htrdiag : (Work.Models.PSL2.diagUnit (Units.mk0 z hz0) :
        Matrix (Fin 2) (Fin 2) F).trace = t := by
      show (!![(z : F), 0; 0, (((Units.mk0 z hz0)⁻¹ : Fˣ) : F)] :
        Matrix (Fin 2) (Fin 2) F).trace = t
      rw [Matrix.trace_fin_two]
      simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.of_apply, Matrix.empty_val', Matrix.cons_val_fin_one, Units.val_inv_eq_inv_val,
        Units.val_mk0]
      rw [htrz]
    obtain ⟨h, hh⟩ := sl2_conj_of_trace_eq (A := A)
      (B := Work.Models.PSL2.diagUnit (Units.mk0 z hz0))
      (by rw [← ht, htrdiag]) (by rw [← ht]; exact htr)
    exact ⟨h, by rw [hh]; exact Work.Models.PSL2.diagUnit_mem (Units.mk0 z hz0)⟩
  · -- `X ^ 2 + t * X + 1` is irreducible: `A` is conjugate into a Singer cycle
    right
    have hanis : Work.Hering.AppVIII.Anisotropic F t := by
      intro a b hab
      by_cases hb : b = 0
      · refine ⟨?_, hb⟩
        have hab' : a * a = 0 := by simpa [hb] using hab
        exact mul_self_eq_zero.mp hab'
      · exfalso
        apply hroot
        refine ⟨a / b, ?_⟩
        field_simp
        linear_combination hab
    obtain ⟨h, hh⟩ := sl2_conj_companion A (by rw [← ht]; exact htr)
    have hqh : h * A * h⁻¹ = (⟨qalphaMat t, by rw [qalphaMat_det]⟩ :
        Matrix.SpecialLinearGroup (Fin 2) F) := by
      rw [← ht] at hh
      exact hh
    refine ⟨singerSubgroup t,
      SingerModelCycle.isCyclic_singerSubgroup hanis,
      SingerModelCycle.card_singerSubgroup hanis, h, ?_⟩
    rw [hqh]
    have halpha : (⟨qalphaMat t, by rw [qalphaMat_det]⟩ :
        Matrix.SpecialLinearGroup (Fin 2) F) = SingerModelCycle.alphaSL t := by
      apply Subtype.ext
      rw [SingerModelCycle.alphaSL_coe]
    rw [halpha]
    exact SingerModelCycle.alphaSL_mem_singerSubgroup t

/-- The order of a cyclic subgroup generated by one element. -/
private lemma card_zpowers {G : Type*} [Group G] [Finite G] (g : G) :
    Nat.card ↥(Subgroup.zpowers g) = orderOf g := by
  let g' : ↥(Subgroup.zpowers g) := ⟨g, Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩⟩
  have hgen : ∀ x : ↥(Subgroup.zpowers g), x ∈ Subgroup.zpowers g' := by
    intro x
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp x.2
    refine Subgroup.mem_zpowers_iff.mpr ⟨n, ?_⟩
    exact Subtype.ext (by simpa using hn)
  have h1 : orderOf g' = Nat.card ↥(Subgroup.zpowers g) :=
    orderOf_eq_card_of_forall_mem_zpowers hgen
  have h2 : orderOf g' = orderOf g := (Subgroup.orderOf_coe g').symm
  rw [← h1]
  exact h2

/-- Conjugation carries `zpowers` to `zpowers`. -/
private lemma zpowers_map_conj {G : Type*} [Group G] (g h : G) :
    (Subgroup.zpowers g).map (MulAut.conj h).toMonoidHom
      = Subgroup.zpowers ((MulAut.conj h) g) := by
  ext y
  constructor
  · intro hy
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    exact Subgroup.mem_zpowers_iff.mpr ⟨n, by simp⟩
  · intro hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact Subgroup.mem_map.mpr ⟨g ^ n, Subgroup.mem_zpowers_iff.mpr ⟨n, rfl⟩, by simp⟩

/-- Any two cyclic subgroups of `SL(2,F)` (`F` a finite field of characteristic `2` with
`4 ≤ Nat.card F`) of order `Nat.card F - 1` are conjugate. -/
theorem sl2_cyclic_conj_card_sub_one {F : Type*} [Field F] [Finite F] [CharP F 2]
    (hq : 4 ≤ Nat.card F)
    {W₁ W₂ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)}
    (h₁ : IsCyclic ↥W₁) (hc₁ : Nat.card ↥W₁ = Nat.card F - 1)
    (h₂ : IsCyclic ↥W₂) (hc₂ : Nat.card ↥W₂ = Nat.card F - 1) :
    ∃ h : Matrix.SpecialLinearGroup (Fin 2) F,
      W₁.map (MulAut.conj h).toMonoidHom = W₂ := by
  have key : ∀ W : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F), IsCyclic ↥W →
      Nat.card ↥W = Nat.card F - 1 →
      ∃ h : Matrix.SpecialLinearGroup (Fin 2) F,
        W.map (MulAut.conj h).toMonoidHom = Work.Models.PSL2.D (F := F) := by
    intro W hcyc hcard
    obtain ⟨g, hg⟩ := hcyc
    have hW : W = Subgroup.zpowers (g : Matrix.SpecialLinearGroup (Fin 2) F) := by
      refine le_antisymm ?_ (Subgroup.zpowers_le.mpr g.2)
      intro y hy
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨y, hy⟩)
      refine Subgroup.mem_zpowers_iff.mpr ⟨n, ?_⟩
      have hcoe := congrArg (fun z : ↥W => (z : Matrix.SpecialLinearGroup (Fin 2) F)) hn
      simpa using hcoe
    have hordG : orderOf (g : Matrix.SpecialLinearGroup (Fin 2) F) = Nat.card F - 1 := by
      rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg, hcard]
    have hx2 : (g : Matrix.SpecialLinearGroup (Fin 2) F) * (g : Matrix.SpecialLinearGroup (Fin 2) F)
        ≠ 1 := by
      intro h1
      have hdvd : Nat.card F - 1 ∣ 2 := by
        rw [← hordG, orderOf_dvd_iff_pow_eq_one]
        simpa [pow_two] using h1
      have hle : Nat.card F - 1 ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
      omega
    have htrace : ((g : Matrix.SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F).trace ≠ 0 := fun h0 =>
      hx2 (sl2_trace_zero_sq_eq_one _ h0)
    rcases sl2_classify (g : Matrix.SpecialLinearGroup (Fin 2) F) with
      h0 | ⟨h, hh⟩ | ⟨W', hcyc', hcard', h, hh⟩
    · exact absurd h0 htrace
    · refine ⟨h, ?_⟩
      rw [hW, zpowers_map_conj]
      refine Subgroup.eq_of_le_of_card_ge ?_ ?_
      · rw [Subgroup.zpowers_le, MulAut.conj_apply]
        exact hh
      · rw [(Work.Models.PSL2.D_facts (F := F)).1, card_zpowers,
          MulEquiv.orderOf_eq (MulAut.conj h) (g : Matrix.SpecialLinearGroup (Fin 2) F), hordG]
    · exfalso
      have h1 : orderOf (h * (g : Matrix.SpecialLinearGroup (Fin 2) F) * h⁻¹) = Nat.card F - 1 := by
        rw [show h * (g : Matrix.SpecialLinearGroup (Fin 2) F) * h⁻¹
            = (MulAut.conj h) (g : Matrix.SpecialLinearGroup (Fin 2) F) from by
          rw [MulAut.conj_apply]]
        rw [MulEquiv.orderOf_eq, hordG]
      have h2 : Nat.card F - 1 ∣ Nat.card F + 1 := by
        have h3 := Subgroup.orderOf_dvd_natCard W' hh
        rw [hcard'] at h3
        rwa [h1] at h3
      have h4 : Nat.card F + 1 - (Nat.card F - 1) = 2 := by omega
      have h5 : Nat.card F - 1 ∣ 2 := by
        have := Nat.dvd_sub h2 (dvd_refl (Nat.card F - 1))
        rwa [h4] at this
      have h6 : Nat.card F - 1 ≤ 2 := Nat.le_of_dvd (by norm_num) h5
      omega
  obtain ⟨h₁', hh₁⟩ := key W₁ h₁ hc₁
  obtain ⟨h₂', hh₂⟩ := key W₂ h₂ hc₂
  refine ⟨h₂'⁻¹ * h₁', ?_⟩
  have hmul : (MulAut.conj (h₂'⁻¹ * h₁')).toMonoidHom
      = ((MulAut.conj h₂'⁻¹).toMonoidHom).comp ((MulAut.conj h₁').toMonoidHom) := by
    ext x
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MonoidHom.comp_apply]
    group
  have hcomp : ((MulAut.conj h₂'⁻¹).toMonoidHom).comp ((MulAut.conj h₂').toMonoidHom)
      = MonoidHom.id (Matrix.SpecialLinearGroup (Fin 2) F) := by
    ext x
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MonoidHom.comp_apply,
      MonoidHom.id_apply]
    group
  rw [hmul, ← Subgroup.map_map, hh₁, ← hh₂, Subgroup.map_map, hcomp, Subgroup.map_id]

/-! ## Auxiliary lemmas for the conjugacy of Singer cycles -/

/-- `X ^ 2 + b * X + 1` has a root in `F` iff `b = z + z⁻¹` for some non-zero `z`. -/
lemma exists_root_iff_sum_inv {F : Type*} [Field F] [CharP F 2] (b : F) :
    (∃ z : F, z * z + b * z + 1 = 0) ↔ ∃ z : F, z ≠ 0 ∧ b = z + z⁻¹ := by
  constructor
  · rintro ⟨z, hz⟩
    have hz0 : z ≠ 0 := by
      rintro rfl
      simp at hz
    have h1 : z * z + b * z = 1 := CharTwo.add_eq_zero.mp hz
    have hmul : b * z = 1 + z * z := by
      have h2 : (z * z + b * z) + z * z = b * z := by
        rw [add_comm (z * z) (b * z), add_assoc, CharTwo.add_self_eq_zero, add_zero]
      rw [← h1, h2]
    refine ⟨z, hz0, ?_⟩
    calc b = b * z * z⁻¹ := by rw [mul_assoc, mul_inv_cancel₀ hz0, mul_one]
      _ = (1 + z * z) * z⁻¹ := by rw [hmul]
      _ = z⁻¹ + z := by rw [add_mul, one_mul, mul_assoc, mul_inv_cancel₀ hz0, mul_one]
      _ = z + z⁻¹ := by ring
  · rintro ⟨z, hz0, rfl⟩
    exact ⟨z, by
      rw [add_mul, mul_comm z⁻¹ z, mul_inv_cancel₀ hz0]
      ring_nf
      simp [CharTwo.two_eq_zero]⟩

/-- The centralizer of the companion matrix `qalphaMat b` (for `b` anisotropic) is the Singer
cycle `singerSubgroup b`. -/
lemma centralizer_alphaSL {F : Type*} [Field F] [Finite F] [CharP F 2] {b : F}
    (hb : Work.Hering.AppVIII.Anisotropic F b) :
    Subgroup.centralizer ({SingerModelCycle.alphaSL b} :
        Set (Matrix.SpecialLinearGroup (Fin 2) F)) = singerSubgroup b := by
  refine le_antisymm ?_ ?_
  · intro g hg
    have hcomm : SingerModelCycle.alphaSL b * g = g * SingerModelCycle.alphaSL b :=
      (Subgroup.mem_centralizer_iff.mp hg) _ rfl
    have hm : (g : Matrix (Fin 2) (Fin 2) F) * qalphaMat b
        = qalphaMat b * (g : Matrix (Fin 2) (Fin 2) F) := by
      have h2 := congrArg (fun u : Matrix.SpecialLinearGroup (Fin 2) F =>
        (u : Matrix (Fin 2) (Fin 2) F)) hcomm
      rw [show ((SingerModelCycle.alphaSL b * g : Matrix.SpecialLinearGroup (Fin 2) F) :
            Matrix (Fin 2) (Fin 2) F)
          = (SingerModelCycle.alphaSL b : Matrix (Fin 2) (Fin 2) F)
            * (g : Matrix (Fin 2) (Fin 2) F) from rfl,
        show ((g * SingerModelCycle.alphaSL b : Matrix.SpecialLinearGroup (Fin 2) F) :
            Matrix (Fin 2) (Fin 2) F)
          = (g : Matrix (Fin 2) (Fin 2) F)
            * (SingerModelCycle.alphaSL b : Matrix (Fin 2) (Fin 2) F) from rfl,
        SingerModelCycle.alphaSL_coe] at h2
      exact h2.symm
    obtain ⟨a, c, hac⟩ :=
      SingerModelCycle.exists_eq_smul_one_add_of_mul_qalphaMat_comm hm
    exact SingerModelCycle.mem_singerSubgroup_of_coe_eq hb hac
  · intro v hv
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    haveI : IsCyclic ↥(singerSubgroup b) := SingerModelCycle.isCyclic_singerSubgroup hb
    haveI : IsMulCommutative ↥(singerSubgroup b) := IsCyclic.isMulCommutative
    have hcomm := congrArg (fun u : ↥(singerSubgroup b) =>
      (u : Matrix.SpecialLinearGroup (Fin 2) F))
      (IsMulCommutative.is_comm.comm (⟨v, hv⟩ : ↥(singerSubgroup b))
        ⟨SingerModelCycle.alphaSL b, SingerModelCycle.alphaSL_mem_singerSubgroup b⟩)
    exact hcomm.symm

/-- For `a b : F` with `a ≠ 0 ≠ b`, `a + a⁻¹ = b + b⁻¹` forces `(a + b) * (a * b + 1) = 0`. -/
private lemma add_inv_eq_key {F : Type*} [Field F] [CharP F 2] {a b : F}
    (ha : a ≠ 0) (hb : b ≠ 0) (h : a + a⁻¹ = b + b⁻¹) :
    (a + b) * (a * b + 1) = 0 := by
  have h2 : (a * b) * (a + a⁻¹) = (a * b) * (b + b⁻¹) := by rw [h]
  have h4 : (a * b) * (a + a⁻¹) = a * a * b + b := by
    rw [mul_add, show (a * b) * a⁻¹ = b by
      rw [mul_assoc, mul_comm b a⁻¹, ← mul_assoc, mul_inv_cancel₀ ha, one_mul]]
    ring
  have h5 : (a * b) * (b + b⁻¹) = a * b * b + a := by
    rw [mul_add, show (a * b) * b⁻¹ = a by rw [mul_assoc, mul_inv_cancel₀ hb, mul_one]]
  rw [h4, h5] at h2
  have hgoal : (a + b) * (a * b + 1) = (a * a * b + b) + (a * b * b + a) := by ring
  rw [hgoal, ← h2]
  exact CharTwo.add_self_eq_zero _

/-- All fibres of `z ↦ z + z⁻¹` on `F` have exactly two elements. -/
private lemma card_fiber_sum_inv {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
    {b : F} (hb : b ∈ Finset.univ.image (fun z : F => z + z⁻¹)) :
    (Finset.univ.filter (fun z : F => z + z⁻¹ = b)).card = 2 := by
  by_cases hb0 : b = 0
  · subst hb0
    have hset : Finset.univ.filter (fun z : F => z + z⁻¹ = 0) = {0, 1} := by
      ext z
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · intro hz
        by_cases hz0 : z = 0
        · exact Or.inl hz0
        · right
          have h1 : z * z + 1 = 0 := by
            simpa only [mul_add, mul_inv_cancel₀ hz0, mul_one, mul_zero] using
              congrArg (fun w : F => z * w) hz
          have h2 : (z + 1) * (z + 1) = 0 := by
            calc (z + 1) * (z + 1) = z * z + (z + z) + 1 := by ring
              _ = z * z + 1 := by rw [CharTwo.add_self_eq_zero, add_zero]
              _ = 0 := h1
          have h3 : z + 1 = 0 := mul_self_eq_zero.mp h2
          exact CharTwo.add_eq_zero.mp h3
      · rintro (rfl | rfl)
        · simp
        · simpa using CharTwo.add_self_eq_zero (1 : F)
    rw [hset, Finset.card_pair zero_ne_one]
  · obtain ⟨z, -, hz⟩ := Finset.mem_image.mp hb
    have hz0 : z ≠ 0 := by
      rintro rfl
      rw [zero_add, _root_.inv_zero] at hz
      exact hb0 hz.symm
    have hset : Finset.univ.filter (fun w : F => w + w⁻¹ = b) = {z, z⁻¹} := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · intro hw
        have hwb : w + w⁻¹ = z + z⁻¹ := by rw [hw, hz]
        by_cases hw0 : w = 0
        · rw [hw0, _root_.inv_zero, add_zero] at hw
          exact absurd hw.symm hb0
        · have hkey := add_inv_eq_key hw0 hz0 hwb
          rcases mul_eq_zero.mp hkey with h | h
          · left
            rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at h
            exact h
          · right
            exact eq_inv_of_mul_eq_one_left (CharTwo.add_eq_zero.mp h)
      · rintro (rfl | h)
        · exact hz
        · rw [h]
          have hzinv : z⁻¹ + (z⁻¹)⁻¹ = z + z⁻¹ := by
            rw [inv_inv]
            exact add_comm _ _
          rw [hzinv]
          exact hz
    have hne : z ≠ z⁻¹ := by
      intro h
      exact hb0 (by rw [← hz, ← h, CharTwo.add_self_eq_zero z])
    rw [hset, Finset.card_pair hne]

/-- The number of `b` with `Anisotropic F b` is half of `Nat.card F`. -/
lemma two_mul_card_anisotropic {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]
    [DecidablePred (fun b : F => Work.Hering.AppVIII.Anisotropic F b)] :
    2 * (Finset.univ.filter (fun b : F => Work.Hering.AppVIII.Anisotropic F b)).card
      = Nat.card F := by
  classical
  have hanis : ∀ b : F, ¬ Work.Hering.AppVIII.Anisotropic F b →
      b ∈ Finset.univ.image (fun z : F => z + z⁻¹) := by
    intro b hb
    rw [Work.Hering.AppVIII.Anisotropic] at hb
    push_neg at hb
    obtain ⟨a, c, hac, hac0⟩ := hb
    have hc : c ≠ 0 := by
      intro hc0
      have h1 : a = 0 := by
        rw [hc0] at hac
        simpa using mul_self_eq_zero.mp (by simpa using hac)
      exact hac0 h1 hc0
    have ha : a ≠ 0 := by
      intro ha0
      have h1 : c = 0 := by
        rw [ha0] at hac
        simpa using mul_self_eq_zero.mp (by simpa using hac)
      exact hc h1
    have hz0 : a * c⁻¹ ≠ 0 := mul_ne_zero ha (inv_ne_zero hc)
    have h1 : a * c⁻¹ * (a * c⁻¹) + b * (a * c⁻¹) + 1 = 0 := by
      have hcc : c * c ≠ 0 := mul_ne_zero hc hc
      have key : (a * c⁻¹ * (a * c⁻¹) + b * (a * c⁻¹) + 1) * (c * c) = 0 := by
        have hid : (a * c⁻¹ * (a * c⁻¹) + b * (a * c⁻¹) + 1) * (c * c)
            = a * a + b * (a * c) + c * c := by
          field_simp
          try ring
        rw [hid]
        exact hac
      exact (mul_eq_zero.mp key).resolve_right hcc
    have h2 : b * (a * c⁻¹) = 1 + a * c⁻¹ * (a * c⁻¹) := by
      have h3 : a * c⁻¹ * (a * c⁻¹) + b * (a * c⁻¹) = 1 :=
        CharTwo.add_eq_zero.mp h1
      have h4 : (a * c⁻¹ * (a * c⁻¹) + b * (a * c⁻¹)) + a * c⁻¹ * (a * c⁻¹)
          = b * (a * c⁻¹) := by
        rw [add_comm (a * c⁻¹ * (a * c⁻¹)) (b * (a * c⁻¹)), add_assoc,
          CharTwo.add_self_eq_zero, add_zero]
      rw [← h3, h4]
    have hbexpr : (1 + a * c⁻¹ * (a * c⁻¹)) * (a * c⁻¹)⁻¹ = b := by
      rw [← h2, mul_assoc, mul_inv_cancel₀ hz0, mul_one]
    exact Finset.mem_image.mpr ⟨a * c⁻¹, Finset.mem_univ _, by
      rw [← hbexpr, add_mul, one_mul, mul_assoc, mul_inv_cancel₀ hz0, mul_one]
      ring⟩
  have himage : ∀ b : F, b ∈ Finset.univ.image (fun z : F => z + z⁻¹) →
      ¬ Work.Hering.AppVIII.Anisotropic F b := by
    intro b hb
    obtain ⟨z, -, hz⟩ := Finset.mem_image.mp hb
    rw [← hz, Work.Hering.AppVIII.Anisotropic]
    push_neg
    rcases eq_or_ne z 0 with hz0 | hz0
    · subst hz0
      refine ⟨1, 1, ?_, ?_⟩
      · simp [CharTwo.add_self_eq_zero]
      · first
        | intro _; exact one_ne_zero
        | rintro ⟨h1, _⟩; exact one_ne_zero h1
    · refine ⟨z, 1, ?_, ?_⟩
      · rw [mul_one, add_mul, mul_comm z⁻¹ z, mul_inv_cancel₀ hz0]
        ring_nf
        simp [CharTwo.two_eq_zero]
      · first
        | intro _; exact one_ne_zero
        | rintro ⟨h1, _⟩; exact one_ne_zero h1
  have hfil : (Finset.univ.filter (fun b : F => ¬ Work.Hering.AppVIII.Anisotropic F b))
      = Finset.univ.image (fun z : F => z + z⁻¹) := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · exact hanis b
    · exact himage b
  have hcompl := Finset.card_filter_add_card_filter_not
    (s := (Finset.univ : Finset F)) (p := fun b : F => Work.Hering.AppVIII.Anisotropic F b)
  rw [hfil, Finset.card_univ] at hcompl
  have hfibsum := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset F)) (t := Finset.univ.image (fun z : F => z + z⁻¹))
    (f := fun z : F => z + z⁻¹)
    (fun z _ => Finset.mem_image_of_mem _ (Finset.mem_univ z))
  rw [Finset.card_univ] at hfibsum
  have htwo : ∑ b ∈ Finset.univ.image (fun z : F => z + z⁻¹),
      (Finset.univ.filter (fun z : F => z + z⁻¹ = b)).card
      = 2 * (Finset.univ.image (fun z : F => z + z⁻¹)).card := by
    rw [Finset.sum_congr rfl (fun b hb => card_fiber_sum_inv hb)]
    rw [Finset.sum_const, smul_eq_mul]
    ring
  rw [htwo] at hfibsum
  rw [Nat.card_eq_fintype_card]
  omega

/-- For `b` anisotropic, the number of elements of `SL(2,F)` of trace `b` is `q * (q - 1)`
(`q = |F|`): the map `x ↦ (x 0 0, x 0 1)` is a bijection onto `F × Fˣ`. -/
lemma card_trace_class {F : Type*} [Field F] [Fintype F] [CharP F 2]
    {b : F} (hb : Work.Hering.AppVIII.Anisotropic F b) :
    Nat.card {x : Matrix.SpecialLinearGroup (Fin 2) F //
      (x : Matrix (Fin 2) (Fin 2) F).trace = b} = Nat.card F * (Nat.card F - 1) := by
  have hne : ∀ M : Matrix (Fin 2) (Fin 2) F, M.det = 1 → M.trace = b → M 0 1 ≠ 0 := by
    intro M hMdet hMtr h0
    have htr : M 0 0 + M 1 1 = b := by
      rw [← hMtr, Matrix.trace_fin_two]
    have h11 : M 1 1 = b + M 0 0 := by
      rw [← htr]
      ring_nf
      simp [CharTwo.two_eq_zero]
    have hdet : M 0 0 * (b + M 0 0) = 1 := by
      rw [Matrix.det_fin_two] at hMdet
      rw [h0, zero_mul, sub_zero, h11] at hMdet
      exact hMdet
    have h2 : M 0 0 * M 0 0 + b * M 0 0 = 1 := by
      calc M 0 0 * M 0 0 + b * M 0 0 = M 0 0 * (b + M 0 0) := by ring
        _ = 1 := hdet
    have h3 : M 0 0 * M 0 0 + b * (M 0 0 * 1) + 1 * 1 = 0 := by
      rw [mul_one, one_mul, h2, CharTwo.add_self_eq_zero]
    exact one_ne_zero (hb (M 0 0) 1 h3).2
  have hdet_form : ∀ p : F × Fˣ,
      p.1 * (p.1 + b) + (p.2 : F) * ((1 + p.1 * (p.1 + b)) / (p.2 : F)) = 1 := by
    intro p
    have h : (p.2 : F) * ((1 + p.1 * (p.1 + b)) / (p.2 : F)) = 1 + p.1 * (p.1 + b) := by
      rw [div_eq_mul_inv, mul_comm ((p.2 : F)), mul_assoc, inv_mul_cancel₀ (Units.ne_zero p.2),
        mul_one]
    rw [h]
    rw [show p.1 * (p.1 + b) + (1 + p.1 * (p.1 + b)) = 1 by
      rw [add_comm (1 : F) (p.1 * (p.1 + b)), ← add_assoc, CharTwo.add_self_eq_zero, zero_add]]
  set f : {x : Matrix.SpecialLinearGroup (Fin 2) F //
        (x : Matrix (Fin 2) (Fin 2) F).trace = b} → {p : F × F // p.2 ≠ 0} :=
    fun x => ⟨((x.1 : Matrix (Fin 2) (Fin 2) F) 0 0,
      (x.1 : Matrix (Fin 2) (Fin 2) F) 0 1), hne _ x.1.2 x.2⟩ with hf
  set g : {p : F × F // p.2 ≠ 0} → {x : Matrix.SpecialLinearGroup (Fin 2) F //
        (x : Matrix (Fin 2) (Fin 2) F).trace = b} :=
    fun p => ⟨⟨!![p.1.1, p.1.2; (1 + p.1.1 * (p.1.1 + b)) / p.1.2, p.1.1 + b], by
        rw [Matrix.det_fin_two_of, sub_eq_add_neg, CharTwo.neg_eq]
        exact hdet_form (p.1.1, Units.mk0 p.1.2 p.2)⟩, by
        rw [Matrix.trace_fin_two]
        exact (show p.1.1 + (p.1.1 + b) = b by
          rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add])⟩ with hg
  have hgf : Function.LeftInverse g f := by
    intro x
    apply Subtype.ext
    apply Subtype.ext
    obtain ⟨xx, hx⟩ := x
    set M : Matrix (Fin 2) (Fin 2) F := (xx : Matrix (Fin 2) (Fin 2) F) with hM
    have hMdet : M.det = 1 := xx.2
    have hMtr : M.trace = b := hx
    have hs : M 0 1 ≠ 0 := hne M hMdet hMtr
    have htr : M 0 0 + M 1 1 = b := by
      rw [← hMtr, Matrix.trace_fin_two]
    have h11 : M 1 1 = b + M 0 0 := by
      rw [← htr]
      ring_nf
      simp [CharTwo.two_eq_zero]
    have hdet : M 0 0 * M 1 1 + M 0 1 * M 1 0 = 1 := by
      rw [Matrix.det_fin_two, sub_eq_add_neg, CharTwo.neg_eq] at hMdet
      exact hMdet
    have hdet2 : M 0 0 * (b + M 0 0) + M 0 1 * M 1 0 = 1 := by
      rw [← hdet, h11]
    have h2 : M 0 1 * M 1 0 = 1 + M 0 0 * (M 0 0 + b) := by
      rw [show (1 : F) + M 0 0 * (M 0 0 + b) = 1 + M 0 0 * (b + M 0 0) by ring]
      rw [← hdet2]
      ring_nf
      simp [CharTwo.two_eq_zero]
    have h10 : M 1 0 = (1 + M 0 0 * (M 0 0 + b)) / M 0 1 := by
      rw [eq_div_iff hs, mul_comm]
      exact h2
    show (!![M 0 0, M 0 1;
        (1 + M 0 0 * (M 0 0 + b)) / M 0 1, M 0 0 + b] : Matrix (Fin 2) (Fin 2) F) = M
    ext i j
    fin_cases i <;> fin_cases j <;> simp
    · exact h10.symm
    · rw [h11]; ring
  have hfg : Function.RightInverse g f := by
    intro p
    apply Subtype.ext
    obtain ⟨⟨p0, p1⟩, hp⟩ := p
    show ((!![p0, p1; (1 + p0 * (p0 + b)) / p1, p0 + b] : Matrix (Fin 2) (Fin 2) F) 0 0,
      (!![p0, p1; (1 + p0 * (p0 + b)) / p1, p0 + b] : Matrix (Fin 2) (Fin 2) F) 0 1) = (p0, p1)
    simp
  have hcard : Nat.card {p : F × F // p.2 ≠ 0} = Nat.card F * (Nat.card F - 1) := by
    have : Nat.card {p : F × F // p.2 ≠ 0} = Nat.card (F × Fˣ) :=
      Nat.card_congr
        { toFun := fun p => (p.1.1, Units.mk0 p.1.2 p.2)
          invFun := fun q => ⟨(q.1, (q.2 : F)), (q.2).ne_zero⟩
          left_inv := fun p => by ext <;> rfl
          right_inv := fun q => by ext <;> rfl }
    rw [this, Nat.card_prod, Nat.card_units]
  have hbij : Nat.card {x : Matrix.SpecialLinearGroup (Fin 2) F //
        (x : Matrix (Fin 2) (Fin 2) F).trace = b} = Nat.card {p : F × F // p.2 ≠ 0} :=
    Nat.card_congr (Equiv.ofBijective f
      (Function.bijective_iff_has_inverse.mpr ⟨g, hgf, hfg⟩))
  rw [hbij, hcard]

/-- If `b` is not anisotropic, `X ^ 2 + b * X + 1` has a root in `F`. -/
lemma exists_root_of_not_anisotropic {F : Type*} [Field F] [CharP F 2]
    {b : F} (hb : ¬ Work.Hering.AppVIII.Anisotropic F b) :
    ∃ z : F, z * z + b * z + 1 = 0 := by
  rw [Work.Hering.AppVIII.Anisotropic] at hb
  push_neg at hb
  obtain ⟨a, c, hac, hac0⟩ := hb
  have hc : c ≠ 0 := by
    intro hc0
    have h : a = 0 := by
      rw [hc0] at hac
      simpa using mul_self_eq_zero.mp (by simpa using hac)
    exact hac0 h hc0
  have ha : a ≠ 0 := by
    intro ha0
    have h : c = 0 := by
      rw [ha0] at hac
      simpa using mul_self_eq_zero.mp (by simpa using hac)
    exact hc h
  have hz0 : a * c⁻¹ ≠ 0 := mul_ne_zero ha (inv_ne_zero hc)
  have hid : a * c⁻¹ * (a * c⁻¹) + b * (a * c⁻¹) + 1 = 0 := by
    have hcc : c * c ≠ 0 := mul_ne_zero hc hc
    have hid2 : (a * c⁻¹ * (a * c⁻¹) + b * (a * c⁻¹) + 1) * (c * c)
        = a * a + b * (a * c) + c * c := by
      field_simp
      try ring
    have hzero : (a * c⁻¹ * (a * c⁻¹) + b * (a * c⁻¹) + 1) * (c * c) = 0 := by
      rw [hid2]; exact hac
    exact (mul_eq_zero.mp hzero).resolve_right hcc
  exact ⟨a * c⁻¹, hid⟩

/-- `u ↦ diag(u, u⁻¹)` as a monoid homomorphism `Fˣ →* SL(2,F)`. -/
noncomputable def diagUnitHom (F : Type*) [Field F] [CharP F 2] :
    Fˣ →* Matrix.SpecialLinearGroup (Fin 2) F where
  toFun := Work.Models.PSL2.diagUnit
  map_one' := by
    apply Subtype.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Work.Models.PSL2.diagUnit]
  map_mul' := by
    intro u v
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Work.Models.PSL2.diagUnit, Matrix.mul_apply, Fin.sum_univ_two, Units.val_mul,
        Units.val_inv_eq_inv_val, _root_.mul_inv_rev] <;> ring

/-- The order of a diagonal unit equals the order of the unit. -/
lemma orderOf_diagUnit {F : Type*} [Field F] [CharP F 2] (u : Fˣ) :
    orderOf (Work.Models.PSL2.diagUnit u) = orderOf u := by
  have hinj : Function.Injective (diagUnitHom F) := by
    intro u v h
    apply Units.ext
    have h' := congrArg (fun z : Matrix.SpecialLinearGroup (Fin 2) F =>
      (z : Matrix (Fin 2) (Fin 2) F) 0 0)
      (show Work.Models.PSL2.diagUnit u = Work.Models.PSL2.diagUnit v from h)
    simpa [Work.Models.PSL2.diagUnit] using h'
  exact orderOf_injective (diagUnitHom F) hinj u

/-- `(h⁻¹ * a * h) ^ k = h⁻¹ * a ^ k * h`. -/
private lemma inv_mul_pow_mul {M : Type*} [Group M] (h a : M) (k : ℕ) :
    (h⁻¹ * a * h) ^ k = h⁻¹ * a ^ k * h := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ, ih, pow_succ]; group

/-- `(alphaSL ε) ^ (q + 1) = 1` for `ε` anisotropic (`q = |F|`). -/
lemma pow_alphaSL {F : Type*} [Field F] [Finite F] [CharP F 2] {ε : F}
    (hε : Work.Hering.AppVIII.Anisotropic F ε) :
    (SingerModelCycle.alphaSL ε) ^ (Nat.card F + 1) = 1 := by
  apply Subtype.ext
  show (SingerModelCycle.alphaSL ε : Matrix (Fin 2) (Fin 2) F) ^ (Nat.card F + 1) = 1
  rw [SingerModelCycle.alphaSL_coe,
    show qalphaMat ε = quadAlgHom ε (Work.Hering.AppVIII.qalpha F ε) from
      (quadAlgHom_qalpha ε).symm,
    ← map_pow]
  have h1 : (Work.Hering.AppVIII.qalpha F ε) ^ (Nat.card F + 1) = 1 := by
    rw [← SingerModelCycle.norm_eq_pow hε (Work.Hering.AppVIII.qalpha F ε),
      SingerModelCycle.norm_qalpha]
    simp
  rw [h1, map_one]

/-- `x ^ (q + 1) = 1` (`q = |F|`) iff `x = 1` or the trace of `x` is anisotropic. -/
lemma pow_qp1_iff {F : Type*} [Field F] [Fintype F] [CharP F 2]
    (x : Matrix.SpecialLinearGroup (Fin 2) F) :
    x ^ (Nat.card F + 1) = 1 ↔
      x = 1 ∨ Work.Hering.AppVIII.Anisotropic F ((x : Matrix (Fin 2) (Fin 2) F).trace) := by
  have hF2 : 2 ≤ Nat.card F := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  have hodd2 : Odd (Nat.card F + 1) := by
    obtain ⟨n, hn, hncard⟩ := FiniteField.card F 2
    rw [Nat.card_eq_fintype_card, hncard]
    obtain ⟨m, hm⟩ : ∃ m : ℕ, (n : ℕ) = m + 1 :=
      ⟨(n : ℕ) - 1, by have h := n.pos; omega⟩
    rw [hm, pow_succ]
    exact ⟨2 ^ m, by ring⟩
  constructor
  · intro hx
    by_cases h1 : x = 1
    · exact Or.inl h1
    · right
      have htrx : (x : Matrix (Fin 2) (Fin 2) F).trace ≠ 0 := by
        intro h0
        apply h1
        have hx2 : x * x = 1 := sl2_trace_zero_sq_eq_one x h0
        have hdvd : orderOf x ∣ 2 := by
          rw [orderOf_dvd_iff_pow_eq_one, pow_two]
          exact hx2
        have hdvd3 : orderOf x ∣ Nat.card F + 1 := by
          rw [orderOf_dvd_iff_pow_eq_one]; exact hx
        have hodd : Odd (orderOf x) := Odd.of_dvd_nat hodd2 hdvd3
        rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h | h
        · exact orderOf_eq_one_iff.mp h
        · rw [h] at hodd
          exact absurd hodd (by decide)
      by_contra hanis
      obtain ⟨z, hz⟩ := exists_root_of_not_anisotropic hanis
      obtain ⟨w, hw0, hw⟩ := (exists_root_iff_sum_inv _).mp ⟨z, hz⟩
      have htrw : (Work.Models.PSL2.diagUnit (Units.mk0 w hw0) :
          Matrix (Fin 2) (Fin 2) F).trace
          = (x : Matrix (Fin 2) (Fin 2) F).trace := by
        have h1' : (Work.Models.PSL2.diagUnit (Units.mk0 w hw0) :
            Matrix (Fin 2) (Fin 2) F).trace = w + w⁻¹ := by
          show (!![(w : F), 0; 0, (((Units.mk0 w hw0)⁻¹ : Fˣ) : F)] :
            Matrix (Fin 2) (Fin 2) F).trace = w + w⁻¹
          rw [Matrix.trace_fin_two]
          simp only [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
            Matrix.of_apply, Matrix.empty_val', Matrix.cons_val_fin_one,
            Units.val_inv_eq_inv_val, Units.val_mk0]
        rw [h1']
        exact hw.symm
      obtain ⟨h, hh⟩ := sl2_conj_of_trace_eq (A := x)
        (B := Work.Models.PSL2.diagUnit (Units.mk0 w hw0)) htrw.symm htrx
      have hord : orderOf x = orderOf (Units.mk0 w hw0) := by
        have h1' := MulEquiv.orderOf_eq (MulAut.conj h) x
        rw [MulAut.conj_apply, hh, orderOf_diagUnit] at h1'
        exact h1'.symm
      have hdvd1 : orderOf (Units.mk0 w hw0) ∣ Nat.card F - 1 := by
        have := orderOf_dvd_natCard (Units.mk0 w hw0)
        rwa [Nat.card_units] at this
      have hdvd2 : orderOf x ∣ Nat.card F + 1 := by
        rw [orderOf_dvd_iff_pow_eq_one]; exact hx
      have h2 : orderOf (Units.mk0 w hw0) ∣ 2 := by
        rw [← hord] at hdvd1
        have hsub : orderOf x ∣ 2 := by
          have h4 := Nat.dvd_sub hdvd2 hdvd1
          rwa [show Nat.card F + 1 - (Nat.card F - 1) = 2 by omega] at h4
        rwa [hord] at hsub
      have hdvd3 : orderOf (Units.mk0 w hw0) ∣ Nat.card F + 1 := by rw [← hord]; exact hdvd2
      have hoddq : Odd (orderOf (Units.mk0 w hw0)) := Odd.of_dvd_nat hodd2 hdvd3
      rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h2' | h2'
      · exact h1 (orderOf_eq_one_iff.mp (hord.trans h2'))
      · rw [h2'] at hoddq
        exact absurd hoddq (by decide)
  · rintro (rfl | hb)
    · simp
    · have hb0 : (x : Matrix (Fin 2) (Fin 2) F).trace ≠ 0 :=
        Work.Hering.AppVIII.eps_ne_zero F hb
      have htr : (x : Matrix (Fin 2) (Fin 2) F).trace
          = (SingerModelCycle.alphaSL ((x : Matrix (Fin 2) (Fin 2) F).trace) :
              Matrix (Fin 2) (Fin 2) F).trace := by
        rw [SingerModelCycle.alphaSL_coe, qalphaMat_trace]
      obtain ⟨h, hh⟩ := sl2_conj_of_trace_eq (A := x)
        (B := SingerModelCycle.alphaSL ((x : Matrix (Fin 2) (Fin 2) F).trace)) htr hb0
      have hx_eq : x = h⁻¹
          * SingerModelCycle.alphaSL ((x : Matrix (Fin 2) (Fin 2) F).trace) * h := by
        rw [← hh]; group
      rw [hx_eq, inv_mul_pow_mul h
        (SingerModelCycle.alphaSL ((x : Matrix (Fin 2) (Fin 2) F).trace)) (Nat.card F + 1),
        pow_alphaSL hb]
      group

/-- The normalizer of a Singer cycle has order `2 (q + 1)`. -/
lemma card_normalizer_singer {F : Type*} [Field F] [Finite F] [CharP F 2] {ε : F}
    (hε : Work.Hering.AppVIII.Anisotropic F ε) :
    Nat.card ↥(Subgroup.normalizer (singerSubgroup ε :
        Set (Matrix.SpecialLinearGroup (Fin 2) F))) = 2 * (Nat.card F + 1) := by
  have hinv : ∀ v ∈ singerSubgroup ε,
      SingerModelCycle.frobSL ε * v * (SingerModelCycle.frobSL ε)⁻¹ ∈ singerSubgroup ε := by
    intro v hv
    rw [SingerModelCycle.frobSL_inv]
    rw [SingerModelCycle.frobSL_mul_mem_mul_frobSL hε hv]
    exact Subgroup.inv_mem _ hv
  rw [SingerModelCycle.normalizer_singerSubgroup hε,
    SingerModelCycle.card_sup_zpowers_of_inverts (singerSubgroup ε) (SingerModelCycle.frobSL ε)
      (SingerModelCycle.frobSL_mul_self ε) (SingerModelCycle.frobSL_notMem_singerSubgroup hε)
      hinv,
    SingerModelCycle.card_singerSubgroup hε]

end Work.ZassenhausSuzuki
