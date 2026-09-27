import Mathlib
import Submission.Work.Mostow.gapA.tubeDefs
import Submission.Work.Mostow.gapA.rotationFormula
import Submission.Work.Mostow.gapA.axisNormDefs
import Submission.Work.Mostow.bdFixIff
import Submission.Work.Mostow.ematSpec
import Submission.Work.Mostow.poAux

/-!
# Fixed boundary points of a rotation about a geodesic

The main lemma `bdFixedRotation` says that if `b₀ ∈ PO 3 1` is a rotation about the geodesic
`geodSet a b` (in the sense of `IsRotationAbout`, i.e. its fixed set in `ℍ³` is exactly that
geodesic), then the fixed point set of `b₀` on the boundary sphere `Sph 3` is exactly `{a, b}`.

The proof is Minkowski linear algebra: `bd b₀ ξ = ξ` (`ξ ∈ Sph 3`) holds iff the null vector
`nvec ξ = (ξ,1)` is an eigenvector of the effective matrix `emat b₀` (`bdFixIff`), while the
hypothesis that `b₀` fixes `geodSet a b` pointwise says that `emat b₀` fixes `nvec a` and
`nvec b` (`emat_fixes_nvec`).  Writing `nvec ξ = α · nvec a + β · nvec b + z` with `z` in the
(positive definite) normal plane `NormSub a b` and applying the eigenvector relation shows

* either the eigenvalue is `≠ 1`, in which case `α = β = 0` and `nvec ξ = z` is a null vector
  of a positive definite plane, hence `0` — impossible;
* or the eigenvalue is `1`, in which case `emat b₀ z = z`; if `z = 0` then `nvec ξ` lies in
  `span (nvec a, nvec b)` and, being null with time coordinate `1`, must equal `nvec a` or
  `nvec b`, so `ξ = a` or `ξ = b`; if `z ≠ 0`, the point of the hyperboloid with lift
  `±(s · nvec a + s · nvec b + z)`, `s = √((1+⟪z,z⟫)/(2(1-⟪a,b⟫)))`, is fixed by `b₀` and off
  `geodSet a b`, contradicting the hypothesis.

This is a gap-A (`n = 3`) ingredient: `bd b₀` has exactly the two fixed points `a`, `b`.
-/

namespace Work.Mostow.gapA

open Submission.Mostow LeanEval.Geometry.MostowRigidity

/-! ## Two auxiliary lemmas -/

/-- **Eigenvector bookkeeping.** If `A` preserves the Minkowski form and fixes two null vectors
`u`, `v` with `mink v u ≠ 0` pointwise, and `X = α · u + β · v + z` with `z` orthogonal to
both `u` and `v`, then the eigenvector relation `A *ᵥ X = μ · X` forces `(1-μ) α = 0`,
`(1-μ) β = 0` and `A *ᵥ z = μ · z`. -/
lemma eigenDataAux {n : ℕ} (A : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ)
    (u v X z : Fin n ⊕ Fin 1 → ℝ) (α β μ : ℝ)
    (hpres : ∀ x y : Fin n ⊕ Fin 1 → ℝ,
      mink (Matrix.mulVec A x) (Matrix.mulVec A y) = mink x y)
    (hu : Matrix.mulVec A u = u) (hv : Matrix.mulVec A v = v)
    (huu : mink u u = 0) (hvv : mink v v = 0) (hvu : mink v u ≠ 0)
    (hzu : mink z u = 0) (hzv : mink z v = 0)
    (hX : X = α • u + β • v + z)
    (hμ : Matrix.mulVec A X = μ • X) :
    (1 - μ) * α = 0 ∧ (1 - μ) * β = 0 ∧ Matrix.mulVec A z = μ • z := by
  have huv_ne : mink u v ≠ 0 := by rw [minkSeg_comm]; exact hvu
  -- the equations obtained by pairing the eigenvector relation with `u` and with `v`
  have hX_u : mink X u = β * mink v u := by
    rw [hX, minkSeg_add_left, minkSeg_add_left, mink_smul_left'', mink_smul_left'', huu, hzu]
    ring
  have hX_v : mink X v = α * mink u v := by
    rw [hX, minkSeg_add_left, minkSeg_add_left, mink_smul_left'', mink_smul_left'', hvv, hzv]
    ring
  have h_u : mink X u = μ * mink X u := by
    have h1 : mink (Matrix.mulVec A X) u = mink X u := by
      have h := hpres X u
      rw [hu] at h
      exact h
    have h2 : mink (μ • X) u = μ * mink X u := by rw [mink_smul_left'']
    have h := congrArg (fun t => mink t u) hμ
    rw [h1, h2] at h
    exact h
  have h_v : mink X v = μ * mink X v := by
    have h1 : mink (Matrix.mulVec A X) v = mink X v := by
      have h := hpres X v
      rw [hv] at h
      exact h
    have h2 : mink (μ • X) v = μ * mink X v := by rw [mink_smul_left'']
    have h := congrArg (fun t => mink t v) hμ
    rw [h1, h2] at h
    exact h
  have hβ0 : (1 - μ) * β = 0 := by
    have hb_eq : β * mink v u = μ * (β * mink v u) := by
      rw [← hX_u]
      exact h_u
    have key : (1 - μ) * (β * mink v u) = 0 := by
      have e : (1 - μ) * (β * mink v u) = β * mink v u - μ * (β * mink v u) := by ring
      rw [e]
      nth_rewrite 1 [hb_eq]
      rw [sub_self]
    rw [← mul_assoc] at key
    rcases mul_eq_zero.mp key with h1 | h1
    · exact h1
    · exact absurd h1 hvu
  have hα0 : (1 - μ) * α = 0 := by
    have ha_eq : α * mink u v = μ * (α * mink u v) := by
      rw [← hX_v]
      exact h_v
    have key : (1 - μ) * (α * mink u v) = 0 := by
      have e : (1 - μ) * (α * mink u v) = α * mink u v - μ * (α * mink u v) := by ring
      rw [e]
      nth_rewrite 1 [ha_eq]
      rw [sub_self]
    rw [← mul_assoc] at key
    rcases mul_eq_zero.mp key with h1 | h1
    · exact h1
    · exact absurd h1 huv_ne
  -- now the normal component
  refine ⟨hα0, hβ0, ?_⟩
  have hμα : μ * α = α := by nlinarith [hα0]
  have hμβ : μ * β = β := by nlinarith [hβ0]
  have h1 : Matrix.mulVec A X = α • u + β • v + Matrix.mulVec A z := by
    rw [hX, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul, hu, hv]
  have h2 : μ • X = α • u + β • v + μ • z := by
    rw [hX, smul_add, smul_add, smul_smul, smul_smul, hμα, hμβ]
  have hμ' : α • u + β • v + Matrix.mulVec A z = α • u + β • v + μ • z := by
    rw [← h1, ← h2]
    exact hμ
  exact add_left_cancel hμ'

/-- **A fixed point off the geodesic.** If the effective matrix of `b₀` fixes the two null
vectors of `a b : Sph 3` and fixes a nonzero vector `z` of the normal plane `NormSub a b`, then
`b₀` has a fixed point in `ℍ³` which is not on the geodesic `geodSet a b`. -/
lemma fixedOffGeodAux (b₀ : PO 3 1)
    (a b : E 3) (ha : a ∈ Sph 3) (hb : b ∈ Sph 3) (hab : a ≠ b)
    (hAu : Matrix.mulVec (emat b₀) (nvec a) = nvec a)
    (hAv : Matrix.mulVec (emat b₀) (nvec b) = nvec b)
    {z : Fin 3 ⊕ Fin 1 → ℝ} (hz : z ∈ NormSub a b) (hz0 : z ≠ 0)
    (hAz : Matrix.mulVec (emat b₀) z = z) :
    ∃ u : E 3, b₀ • u = u ∧ u ∉ geodSet a b := by
  set δ : ℝ := 1 - inner ℝ a b with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; linarith [inner_ab_lt_one a b ha hb hab]
  have hδne : δ ≠ 0 := ne_of_gt hδpos
  have hδ' : inner ℝ a b - 1 = -δ := by rw [hδdef]; ring
  have huu : mink (nvec a) (nvec a) = 0 := mink_nvec_self' ha
  have hvv : mink (nvec b) (nvec b) = 0 := mink_nvec_self' hb
  have hab_m : mink (nvec a) (nvec b) = inner ℝ a b - 1 := mink_nvec_nvec' a b
  have hba_m : mink (nvec b) (nvec a) = inner ℝ a b - 1 := mink_nvec_b_a
  have hz_a : mink (nvec a) z = 0 := by rw [minkSeg_comm]; exact hz.1
  have hz_b : mink (nvec b) z = 0 := by rw [minkSeg_comm]; exact hz.2
  have hzz : 0 ≤ mink z z := mink_nonneg_of_mem_NormSub ha hz
  set s : ℝ := Real.sqrt ((1 + mink z z) / (2 * δ)) with hsdef
  have hs2 : s ^ 2 = (1 + mink z z) / (2 * δ) := by
    rw [hsdef]; exact Real.sq_sqrt (by positivity)
  set Y : Fin 3 ⊕ Fin 1 → ℝ := s • nvec a + s • nvec b + z with hYdef
  have hAA : mink (s • nvec a + s • nvec b) (s • nvec a + s • nvec b) = -2 * s ^ 2 * δ := by
    rw [mink_expand2 (nvec a) (nvec b) s s s s, huu, hvv, hab_m, hba_m, hδ']
    ring
  have hAz0 : mink (s • nvec a + s • nvec b) z = 0 := by
    rw [minkSeg_add_left, mink_smul_left'', mink_smul_left'', hz_a, hz_b]; ring
  have hzA0 : mink z (s • nvec a + s • nvec b) = 0 := by rw [minkSeg_comm]; exact hAz0
  have hYself : mink Y Y = -1 := by
    have h2s2d : 2 * s ^ 2 * δ = 1 + mink z z := by rw [hs2]; field_simp
    rw [hYdef]
    simp only [minkSeg_add_left, minkSeg_add_right, mink_smul_left'', mink_smul_right'',
      huu, hvv, hab_m, hba_m, hz_a, hz_b, hz.1, hz.2, hδ']
    linarith
  have hYtime_ne : Y (Sum.inr 0) ≠ 0 := by
    intro h0
    have h1 : mink Y Y = (∑ i : Fin 3, Y (Sum.inl i) ^ 2) - Y (Sum.inr 0) ^ 2 := by
      rw [mink_eq_mform]; exact mform_self_apply Y
    have h2 : (0 : ℝ) ≤ ∑ i : Fin 3, Y (Sum.inl i) ^ 2 :=
      Finset.sum_nonneg (fun i _ => sq_nonneg _)
    have h3 : Y (Sum.inr 0) ^ 2 = 0 := by rw [h0]; ring
    rw [hYself, h3, sub_zero] at h1
    linarith
  have hYu : Matrix.mulVec (emat b₀) (s • nvec a + s • nvec b + z)
      = s • nvec a + s • nvec b + z := by
    rw [Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
      hAu, hAv, hAz]
  have hAY : Matrix.mulVec (emat b₀) Y = Y := by rw [hYdef]; exact hYu
  obtain ⟨ρ, hρ1, hρ2, hρpos⟩ :
      ∃ ρ : ℝ, (ρ = 1 ∨ ρ = -1) ∧ ρ ^ 2 = 1 ∧ 0 < (ρ • Y) (Sum.inr 0) := by
    by_cases h : 0 < Y (Sum.inr 0)
    · exact ⟨1, Or.inl rfl, by norm_num, by simpa using h⟩
    · have hle : Y (Sum.inr 0) ≤ 0 := not_lt.mp h
      have hlt : Y (Sum.inr 0) < 0 := lt_of_le_of_ne hle hYtime_ne
      exact ⟨-1, Or.inr rfl, by norm_num, by simpa using hlt⟩
  set Y' : Fin 3 ⊕ Fin 1 → ℝ := ρ • Y with hY'def
  have hY'self : mink Y' Y' = -1 := by
    rw [hY'def, minkSeg_smul, hYself]; nlinarith [hρ2]
  have hAY' : Matrix.mulVec (emat b₀) Y' = Y' := by
    rw [hY'def, Matrix.mulVec_smul]
    exact congrArg (fun t => ρ • t) hAY
  set u' : E 3 := WithLp.toLp 2 (fun i => Y' (Sum.inl i)) with hu'def
  have hliftu' : hlift u' = Y' := by
    rw [hu'def]
    exact (eq_hlift_of_upper Y' (by rw [← mink_eq_mform]; exact hY'self) hρpos).symm
  refine ⟨u', ?_, ?_⟩
  · have hstep : hlift (b₀ • u') = hlift u' := by
      rw [← emat_hlift b₀ u', hliftu']
      exact hAY'
    exact hlift_injective hstep
  · intro hgeo
    have hN : gcN a b u' = 0 := (gcN_eq_zero_iff a b ha hb hab u').mpr hgeo
    have hmink_a : mink (nvec a) Y = -s * δ := by
      rw [hYdef, minkSeg_add_right, minkSeg_add_right, mink_smul_right'', mink_smul_right'',
        huu, hab_m, hz_a, hδ']
      ring
    have hmink_b : mink (nvec b) Y = -s * δ := by
      rw [hYdef, minkSeg_add_right, minkSeg_add_right, mink_smul_right'', mink_smul_right'',
        hvv, hba_m, hz_b, hδ']
      ring
    have hlev_a : lev a u' = ρ * s * δ := by
      rw [lev_eq_neg_mink, hliftu', hY'def, mink_smul_right'', hmink_a]; ring
    have hlev_b : lev b u' = ρ * s * δ := by
      rw [lev_eq_neg_mink, hliftu', hY'def, mink_smul_right'', hmink_b]; ring
    have hgcA : gcA a b u' = ρ * s := by
      have h1 : gcA a b u' = (ρ * s * δ) / δ := by rw [gcA, hlev_b, two_gcL, ← hδdef]
      rw [h1]; exact mul_div_cancel_right₀ _ hδne
    have hgcB : gcB a b u' = ρ * s := by
      have h1 : gcB a b u' = (ρ * s * δ) / δ := by rw [gcB, hlev_a, two_gcL, ← hδdef]
      rw [h1]; exact mul_div_cancel_right₀ _ hδne
    have hgcN : gcN a b u' = ρ • z := by
      funext k
      rw [gcN, hliftu', hY'def, hgcA, hgcB, hYdef]
      simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
      ring
    rw [hgcN] at hN
    exact hz0 (by
      rcases smul_eq_zero.mp hN with h | h
      · rw [h] at hρ2; norm_num at hρ2
      · exact h)

/-! ## The main statement -/

theorem bdFixedRotation (hA : Submission.Mostow.POActionProp 3) (hI : Submission.Mostow.HypIsometryProp 3)
    (a b : Submission.Mostow.E 3) (ha : a ∈ Submission.Mostow.Sph 3) (hb : b ∈ Submission.Mostow.Sph 3)
    (hab : a ≠ b) (M : ℕ) (hM : 0 < M) (b₀ : LeanEval.Geometry.MostowRigidity.PO 3 1)
    (hrot : Work.Mostow.IsRotationAbout b₀ a b (2 * Real.pi / (M : ℝ))) :
    ∀ ξ : Submission.Mostow.E 3, ξ ∈ Submission.Mostow.Sph 3 →
      (Submission.Mostow.bd b₀ ξ = ξ ↔ ξ = a ∨ ξ = b) := by
  intro ξ hξ
  have hax : ∀ u : E 3, u ∈ geodSet a b → b₀ • u = u := fun u hu => (hrot.1 u).mpr hu
  obtain ⟨hAu, hAv⟩ := emat_fixes_nvec hA hI b₀ a b ha hb hab hax
  have hbd_a : bd b₀ a = a :=
    (bdFixIff 3 (by norm_num) hA b₀ a ha).mpr ⟨1, one_ne_zero, by rw [one_smul]; exact hAu⟩
  have hbd_b : bd b₀ b = b :=
    (bdFixIff 3 (by norm_num) hA b₀ b hb).mpr ⟨1, one_ne_zero, by rw [one_smul]; exact hAv⟩
  have huu : mink (nvec a) (nvec a) = 0 := mink_nvec_self' ha
  have hvv : mink (nvec b) (nvec b) = 0 := mink_nvec_self' hb
  have hvu : mink (nvec b) (nvec a) ≠ 0 := by
    rw [mink_nvec_b_a]
    intro h
    exact hab ((inner_eq_one_iff_of_norm_eq_one ((mem_Sph_iff a).mp ha)
      ((mem_Sph_iff b).mp hb)).mp (sub_eq_zero.mp h))
  have hpres : ∀ x y : Fin 3 ⊕ Fin 1 → ℝ,
      mink (Matrix.mulVec (emat b₀) x) (Matrix.mulVec (emat b₀) y) = mink x y :=
    (ematSpec b₀).2.1
  constructor
  · intro hfix
    obtain ⟨μ, hμne, hμeq⟩ := (bdFixIff 3 (by norm_num) hA b₀ ξ hξ).mp hfix
    -- the decomposition `nvec ξ = α · nvec a + β · nvec b + z` with `z ⊥ nvec a, nvec b`
    set δ : ℝ := 1 - inner ℝ a b with hδdef
    have hδne : δ ≠ 0 := by
      rw [hδdef]; linarith [inner_ab_lt_one a b ha hb hab]
    have hδ' : inner ℝ a b - 1 = -δ := by rw [hδdef]; ring
    have hab_m : mink (nvec a) (nvec b) = inner ℝ a b - 1 := mink_nvec_nvec' a b
    have hba_m : mink (nvec b) (nvec a) = inner ℝ a b - 1 := mink_nvec_b_a
    set α : ℝ := -(mink (nvec ξ) (nvec b)) / δ with hαdef
    set β : ℝ := -(mink (nvec ξ) (nvec a)) / δ with hβdef
    set z : Fin 3 ⊕ Fin 1 → ℝ := nvec ξ - α • nvec a - β • nvec b with hzdef
    have hαδ : α * δ = -mink (nvec ξ) (nvec b) := by
      rw [hαdef]; exact div_mul_cancel₀ _ hδne
    have hβδ : β * δ = -mink (nvec ξ) (nvec a) := by
      rw [hβdef]; exact div_mul_cancel₀ _ hδne
    have hzu : mink z (nvec a) = 0 := by
      have e1 : mink z (nvec a)
          = mink (nvec ξ) (nvec a) - α * mink (nvec a) (nvec a) - β * mink (nvec b) (nvec a) := by
        rw [hzdef, mink_sub_left', mink_sub_left', mink_smul_left'', mink_smul_left'']
      rw [e1, huu, hba_m, hδ']
      have hb1 : β * (-δ) = mink (nvec ξ) (nvec a) := by rw [mul_neg, hβδ, neg_neg]
      rw [hb1]; ring
    have hzv : mink z (nvec b) = 0 := by
      have e1 : mink z (nvec b)
          = mink (nvec ξ) (nvec b) - α * mink (nvec a) (nvec b) - β * mink (nvec b) (nvec b) := by
        rw [hzdef, mink_sub_left', mink_sub_left', mink_smul_left'', mink_smul_left'']
      rw [e1, hvv, hab_m, hδ']
      have ha1 : α * (-δ) = mink (nvec ξ) (nvec b) := by rw [mul_neg, hαδ, neg_neg]
      rw [ha1]; ring
    have hzmem : z ∈ NormSub a b := mem_NormSub.mpr ⟨hzu, hzv⟩
    have hdec : nvec ξ = α • nvec a + β • nvec b + z := by rw [hzdef]; abel
    obtain ⟨hα0, hβ0, hAz⟩ :=
      eigenDataAux (emat b₀) (nvec a) (nvec b) (nvec ξ) z α β μ hpres hAu hAv
        huu hvv hvu hzu hzv hdec hμeq
    by_cases hμ1 : μ = 1
    · have hAzz : Matrix.mulVec (emat b₀) z = z := by rw [hAz, hμ1, one_smul]
      by_cases hz0 : z = 0
      · -- `nvec ξ` lies in the span of the two null vectors
        have hX : nvec ξ = α • nvec a + β • nvec b := by rw [hdec, hz0, add_zero]
        have hαβ : α * β = 0 := by
          have h1 : mink (α • nvec a + β • nvec b) (α • nvec a + β • nvec b)
              = 2 * α * β * (inner ℝ a b - 1) := by
            rw [mink_expand2 (nvec a) (nvec b) α β α β, huu, hvv, hab_m, hba_m]
            ring
          rw [← hX, mink_nvec_self' hξ] at h1
          rcases mul_eq_zero.mp (show α * β * (inner ℝ a b - 1) = 0 by linarith) with h | h
          · exact h
          · exact absurd h (by intro hc; linarith [inner_ab_lt_one a b ha hb hab, hc])
        have htime : α + β = 1 := by
          have h := congrFun hX (Sum.inr 0)
          simpa [Work.Mostow.nvec, Pi.add_apply, Pi.smul_apply] using h.symm
        rcases mul_eq_zero.mp hαβ with hα | hβ
        · right
          have hβ1 : β = 1 := by linarith
          have hb' : nvec ξ = nvec b := by rw [hX, hα, hβ1]; simp
          ext i
          have h := congrFun hb' (Sum.inl i)
          simpa [Work.Mostow.nvec] using h
        · left
          have hα1 : α = 1 := by linarith
          have ha' : nvec ξ = nvec a := by rw [hX, hβ, hα1]; simp
          ext i
          have h := congrFun ha' (Sum.inl i)
          simpa [Work.Mostow.nvec] using h
      · -- the normal part is non-zero: `b₀` fixes a point off the geodesic
        exfalso
        obtain ⟨u, hfixu, hgeo⟩ := fixedOffGeodAux b₀ a b ha hb hab hAu hAv hzmem hz0 hAzz
        exact hgeo ((hrot.1 u).mp hfixu)
    · -- non-trivial eigenvalue: `nvec ξ = z` is a null vector of a positive definite plane
      exfalso
      have hα0' : α = 0 := by
        rcases mul_eq_zero.mp hα0 with h | h
        · exact absurd h (by intro hc; exact hμ1 (by linarith))
        · exact h
      have hβ0' : β = 0 := by
        rcases mul_eq_zero.mp hβ0 with h | h
        · exact absurd h (by intro hc; exact hμ1 (by linarith))
        · exact h
      have hXz : nvec ξ = z := by rw [hdec, hα0', hβ0']; simp
      have hznull : mink z z = 0 := by rw [← hXz]; exact mink_nvec_self' hξ
      have hz0 : z = 0 := eq_zero_of_mem_NormSub_of_mink_self_eq_zero ha hb hab hzmem hznull
      exact nvec_ne_zero ξ (by rw [hXz, hz0])
  · rintro (rfl | rfl)
    · exact hbd_a
    · exact hbd_b

end Work.Mostow.gapA
