import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Vero
import Submission.Work.HP.Vero.SigmaDefs
import Submission.Work.HP.Vero.span_realify_latOrth_inf
import Submission.Work.HP.Vero.orth_witness
import Submission.Work.HP.Vero.dualLat_int_shift
import Submission.Work.HP.Vero.dualLat_nonempty
import Submission.Work.HP.Vero.LamAux
import Submission.Work.HP.Sig2.GamTwoDefs
import Submission.Work.HP.Sig2.DminPairLe
import Submission.Work.HP.Sig2.PerpCompLemmas
import Submission.Work.HP.Sig2.CovolumeSingle
import Submission.Work.HP.Sig2.PerpCompSigmaGe
import Submission.Work.HP.Sig2.RowWitness

set_option autoImplicit false
noncomputable section

open Work.HP Finset

namespace Work.HP.Sig2

/-! # Elementary facts used in the assembly of `GamTwo_dual_lam1` -/

/-- The linear functional `v ↦ dotR b v`. -/
def dotLin {ι : Type*} [Fintype ι] (b : ι → ℝ) : (ι → ℝ) →ₗ[ℝ] ℝ where
  toFun v := dotR b v
  map_add' u v := by
    simp only [dotR, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c u := by
    simp only [dotR, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun i _ => by ring)

@[simp] lemma dotLin_apply {ι : Type*} [Fintype ι] (b v : ι → ℝ) : dotLin b v = dotR b v := rfl

/-- If `b` is orthogonal to a generating set, it is orthogonal to its span. -/
lemma dotR_eq_zero_of_mem_span {ι : Type*} [Fintype ι] {S : Set (ι → ℝ)} {b : ι → ℝ}
    (h : ∀ s ∈ S, dotR b s = 0) : ∀ v ∈ Submodule.span ℝ S, dotR b v = 0 := by
  have hle : Submodule.span ℝ S ≤ LinearMap.ker (dotLin b) := by
    rw [Submodule.span_le]
    intro s hs
    exact h s hs
  intro v hv
  exact hle hv

lemma rNorm_smul' {ι : Type*} [Fintype ι] (c : ℝ) (v : ι → ℝ) :
    rNorm (c • v) = |c| * rNorm v := by
  have h1 : (∑ i, (c • v) i ^ 2) = c ^ 2 * ∑ i, v i ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    simp only [Pi.smul_apply, smul_eq_mul, mul_pow]
  rw [rNorm, rNorm, h1, Real.sqrt_mul (by positivity), Real.sqrt_sq_eq_abs]

lemma gcdMinors2_comm {ι : Type*} [Fintype ι] (x y : ι → ℤ) :
    gcdMinors2 y x = gcdMinors2 x y := by
  rw [gcdMinors2, gcdMinors2]
  have h1 : (fun ij : ι × ι => y ij.1 * x ij.2 - y ij.2 * x ij.1)
      = fun ij : ι × ι => (-1) * (x ij.1 * y ij.2 - x ij.2 * y ij.1) := by
    funext ij; ring
  rw [h1, Finset.gcd_mul_left, Work.HP.Lat.normalize_int_eq_natAbs]
  norm_num

/-- `dmin r S` is nonnegative. -/
private lemma dmin_nonneg {ι : Type*} [Fintype ι] [DecidableEq ι] (r : ℕ) (S : Set (ι → ℤ)) :
    0 ≤ dmin r S := by
  rw [dmin]
  exact Real.sInf_nonneg (fun _ ⟨L, _, _, hD⟩ => hD ▸ detL_nonneg L)

/-- `dmin r S ≤ detL M` for a rank-`r` lattice `M` containing `S`. -/
lemma dmin_le_detL {ι : Type*} [Fintype ι] [DecidableEq ι] {r : ℕ} {S : Set (ι → ℤ)}
    {M : Submodule ℤ (ι → ℤ)} (hr : rk M = r) (hS : S ⊆ M) : dmin r S ≤ detL M := by
  rw [dmin]
  refine csInf_le ⟨0, fun D ⟨L, _, _, hD⟩ => hD ▸ detL_nonneg L⟩ ⟨M, hr, hS, rfl⟩

/-- `dotR` against a realified integer vector, unfolded. -/
@[simp] lemma dotR_toR {ι : Type*} [Fintype ι] (a : ι → ℝ) (v : ι → ℤ) :
    dotR a (toR v) = ∑ i, a i * (v i : ℝ) := rfl

lemma dotR_smul_left' {ι : Type*} [Fintype ι] (c : ℝ) (v w : ι → ℝ) :
    dotR (c • v) w = c * dotR v w := by
  rw [dotR, dotR, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

lemma dotR_comm' {ι : Type*} [Fintype ι] (v w : ι → ℝ) : dotR v w = dotR w v :=
  Finset.sum_congr rfl (fun i _ => mul_comm _ _)

/-- The `ℤ`-level pairing identity for the quadratic-form vector `σ(u,u')`. -/
lemma sigma_mul_veronese {n : ℕ} (u u' z : Fin (n + 1) → ℤ) :
    (∑ i, Vero.sigma n u u' i * (veronese 2 n z) i)
      = (∑ i, z i * u i) * (∑ i, z i * u' i) := by
  rw [show (∑ i, Vero.sigma n u u' i * (veronese 2 n z) i)
      = ∑ m, (veronese 2 n z) m * Vero.sigma n u u' m from
    Finset.sum_congr rfl (fun i _ => mul_comm _ _)]
  exact Vero.dot_veronese_sigma n z u u'

/-- The real pairing of the quadratic-form vector `σ(u,u')` against `ν₂(z)`. -/
lemma dotR_toR_sigma {n : ℕ} (u u' z : Fin (n + 1) → ℤ) :
    dotR (toR (Vero.sigma n u u')) (toR (veronese 2 n z))
      = ((∑ i, z i * u i : ℤ) : ℝ) * ((∑ i, z i * u' i : ℤ) : ℝ) := by
  rw [dotR_toR]
  simp only [toR]
  rw [show (∑ i, (Vero.sigma n u u') i * ((veronese 2 n z) i : ℝ))
      = ((∑ m, (veronese 2 n z) m * (Vero.sigma n u u') m : ℤ) : ℝ) from by
    push_cast
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)]
  rw [Vero.dot_veronese_sigma]
  push_cast
  ring

/-! ## Orthogonality of dual vectors with `V₂` -/

/-- An element of the dual lattice of `Gam 2 n x y` is orthogonal to `V₂`, i.e. to
`span_ℝ{ν₂(x), ν₂(y)}` (the real span of `Q2 n x y`). -/
theorem dotR_dualLat_V2R {n : ℕ} {x y : Fin (n + 1) → ℤ} {a : Mon 2 n → ℝ}
    (ha : a ∈ dualLat (realify (Gam 2 n x y))) :
    ∀ v ∈ V2R n x y, dotR a v = 0 := by
  have hspan : Submodule.span ℝ (realify (Gam 2 n x y) : Set (Mon 2 n → ℝ))
      = (Fintype.linearCombination ℝ (fun i => ((veronese 2 n x) i : ℝ))).ker ⊓
        (Fintype.linearCombination ℝ (fun i => ((veronese 2 n y) i : ℝ))).ker := by
    rw [show realify (Gam 2 n x y)
        = ((latOrth (veronese 2 n x) ⊓ latOrth (veronese 2 n y)).map intCastPi) from rfl]
    exact Work.HP.Vero.span_realify_latOrth_inf _ _
  have ha1 : a ∈ Submodule.span ℝ (realify (Gam 2 n x y) : Set (Mon 2 n → ℝ)) := ha.1
  rw [hspan] at ha1
  have hx0 : dotR a (toR (veronese 2 n x)) = 0 := by
    have h : (Fintype.linearCombination ℝ (fun i => ((veronese 2 n x) i : ℝ))) a = 0 := ha1.1
    rw [Fintype.linearCombination_apply] at h
    simp only [smul_eq_mul] at h
    rw [dotR_toR]
    exact h
  have hy0 : dotR a (toR (veronese 2 n y)) = 0 := by
    have h : (Fintype.linearCombination ℝ (fun i => ((veronese 2 n y) i : ℝ))) a = 0 := ha1.2
    rw [Fintype.linearCombination_apply] at h
    simp only [smul_eq_mul] at h
    rw [dotR_toR]
    exact h
  intro v hv
  rw [V2R] at hv
  refine dotR_eq_zero_of_mem_span ?_ v hv
  rintro s (rfl | rfl)
  · exact hx0
  · exact hy0

/-- A dual vector is orthogonal to `Q2 n x y`. -/
theorem dotR_dualLat_Q2 {n : ℕ} {x y : Fin (n + 1) → ℤ} {a : Mon 2 n → ℝ}
    (ha : a ∈ dualLat (realify (Gam 2 n x y))) :
    ∀ q ∈ Q2 n x y, dotR a (toR q) = 0 := by
  intro q hq
  rw [toR_eq_intCastPi]
  exact dotR_dualLat_V2R ha (intCastPi q) ((mem_Q2_iff n x y q).mp hq)

/-- The row map of `ν₂(x)` is `xᵢ • x`. -/
lemma rowVecR_veronese (n : ℕ) (i : Fin (n + 1)) (x : Fin (n + 1) → ℤ) :
    rowVecR n i (toR (veronese 2 n x)) = (x i : ℝ) • toR x := by
  ext j
  simp only [rowVecR, Vero.veronese_pairMon, Pi.smul_apply, toR]
  push_cast
  ring

/-! ## The first case of the dichotomy -/

/-- **First case.** If a nonzero element `a` of the dual of `Γ = Λ_{ν₂(x)} ∩ Λ_{ν₂(y)}` lies in
`V₃ = span_ℝ{ν₂(x), ν₂(y), ν₂(x+y)}`, then `(1/3) 𝔡₂(x,y)²/(‖x‖‖y‖) ≤ ‖a‖`. -/
theorem caseOne {n : ℕ} (x y : Fin (n + 1) → ℤ) (hx : IsPrim x) (hy : IsPrim y)
    (hxy : LinearIndependent ℤ ![x, y]) (a : Mon 2 n → ℝ)
    (ha : a ∈ dualLat (realify (Gam 2 n x y))) (ha0 : a ≠ 0) (hV3 : a ∈ V3R n x y) :
    (1 / 3) * (dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) ^ 2 / (eNorm x * eNorm y))
      ≤ rNorm a := by
  classical
  set G : ℤ := gcdMinors2 x y with hG
  have hGpos : 0 < G := (DminPairLe x y hxy).2
  have hGne : (G : ℝ) ≠ 0 := by exact_mod_cast ne_of_gt hGpos
  have hGposR : (0 : ℝ) < (G : ℝ) := by exact_mod_cast hGpos
  -- the properties of `perpComp` for `Λ = Q2`
  obtain ⟨hp1, -, -, hkillspan, -, -, hsmul, hadd⟩ :=
    PerpCompLemmas (Q2 n x y) (toR (veronese 2 n (x + y))) (toR (veronese 2 n (x + y)))
      (by simp)
  have haQ : ∀ q ∈ Q2 n x y, dotR a (toR q) = 0 := dotR_dualLat_Q2 ha
  have hpa : perpComp (Q2 n x y) a = a :=
    ((PerpCompLemmas (Q2 n x y) a a (by simp)).2.2.1) haQ
  have hzero : perpComp (Q2 n x y) (0 : Mon 2 n → ℝ) = 0 := by
    have h := hsmul (0 : ℝ) (0 : Mon 2 n → ℝ)
    simpa using h
  have hνx : perpComp (Q2 n x y) (toR (veronese 2 n x)) = 0 := by
    refine hkillspan _ ?_
    rw [span_intCast_Q2]
    exact Submodule.subset_span (by simp)
  have hνy : perpComp (Q2 n x y) (toR (veronese 2 n y)) = 0 := by
    refine hkillspan _ ?_
    rw [span_intCast_Q2]
    exact Submodule.subset_span (by simp)
  -- decompose `a` along `V₃ = span{ν₂x, ν₂y, ν₂(x+y)}`
  have hdecomp : ∃ γ : ℝ, perpComp (Q2 n x y) a
      = γ • perpComp (Q2 n x y) (toR (veronese 2 n (x + y))) := by
    have hmem : a ∈ Submodule.span ℝ ({toR (veronese 2 n x), toR (veronese 2 n y),
        toR (veronese 2 n (x + y))} : Set (Mon 2 n → ℝ)) := by
      simpa only [V3R] using hV3
    refine Submodule.span_induction (p := fun v _ =>
      ∃ γ : ℝ, perpComp (Q2 n x y) v = γ • perpComp (Q2 n x y) (toR (veronese 2 n (x+y))))
      ?_ ?_ ?_ ?_ hmem
    · intro s hs
      rcases hs with rfl | rfl | rfl
      · exact ⟨0, by rw [hνx, zero_smul]⟩
      · exact ⟨0, by rw [hνy, zero_smul]⟩
      · exact ⟨1, by rw [one_smul]⟩
    · exact ⟨0, by rw [hzero, zero_smul]⟩
    · intro u v _ _ hu hv
      obtain ⟨c, hc⟩ := hu
      obtain ⟨d, hd⟩ := hv
      exact ⟨c + d, by rw [hadd, hc, hd, add_smul]⟩
    · intro c u _ hu
      obtain ⟨d, hd⟩ := hu
      exact ⟨c * d, by rw [hsmul, hd, smul_smul]⟩
  obtain ⟨γ, hγ⟩ := hdecomp
  have ha' : a = γ • perpComp (Q2 n x y) (toR (veronese 2 n (x + y))) := by
    rw [← hpa]; exact hγ
  have hγne : γ ≠ 0 := by
    intro h0
    refine ha0 ?_
    rw [ha', h0, zero_smul]
  -- the Bézout-type witnesses
  obtain ⟨u, hu_x, hu_y⟩ := Vero.orth_witness x y hxy
  have hxy' : LinearIndependent ℤ ![y, x] := by
    rw [LinearIndependent.pair_iff] at hxy ⊢
    intro s t hst
    obtain ⟨h1, h2⟩ := hxy t s (by simpa [add_comm] using hst)
    exact ⟨h2, h1⟩
  obtain ⟨u', hu'_y, hu'_x⟩ := Vero.orth_witness y x hxy'
  have hGyx : gcdMinors2 y x = gcdMinors2 x y := (gcdMinors2_comm y x).symm
  rw [hGyx] at hu'_x
  have hσx : (∑ i, x i * u i) = 0 := by
    rw [show (∑ i, x i * u i) = ∑ i, u i * x i from
      Finset.sum_congr rfl (fun i _ => mul_comm _ _), hu_x]
  have hσy : (∑ i, y i * u i) = G := by
    rw [show (∑ i, y i * u i) = ∑ i, u i * y i from
      Finset.sum_congr rfl (fun i _ => mul_comm _ _), hu_y]
  have hσx' : (∑ i, x i * u' i) = G := by
    rw [show (∑ i, x i * u' i) = ∑ i, u' i * x i from
      Finset.sum_congr rfl (fun i _ => mul_comm _ _), hu'_x]
  have hσy' : (∑ i, y i * u' i) = 0 := by
    rw [show (∑ i, y i * u' i) = ∑ i, u' i * y i from
      Finset.sum_congr rfl (fun i _ => mul_comm _ _), hu'_y]
  -- the product conditions for the two Veronese generators
  have hpx : (∑ i, x i * u i) * (∑ i, x i * u' i) = 0 := by rw [hσx, zero_mul]
  have hpy : (∑ i, y i * u i) * (∑ i, y i * u' i) = 0 := by rw [hσy', mul_zero]
  -- σ(u,u') lies in Γ
  have hnu_mem : Vero.sigma n u u' ∈ Gam 2 n x y := by
    rw [Gam, Submodule.mem_inf]
    refine ⟨?_, ?_⟩
    · rw [latOrth, LinearMap.mem_ker, Fintype.linearCombination_apply]
      simp only [smul_eq_mul]
      rw [sigma_mul_veronese u u' x, hpx]
    · rw [latOrth, LinearMap.mem_ker, Fintype.linearCombination_apply]
      simp only [smul_eq_mul]
      rw [sigma_mul_veronese u u' y, hpy]
  -- σ(u,u') ⊥ Q2
  have hgen : ∀ z : Fin (n + 1) → ℤ, (∑ i, z i * u i) * (∑ i, z i * u' i) = 0 →
      dotR (toR (Vero.sigma n u u')) (toR (veronese 2 n z)) = 0 := by
    intro z h
    rw [dotR_toR_sigma u u' z]
    rw [← Int.cast_mul, h]
    simp
  have hnu_orthQ : ∀ q ∈ Q2 n x y, dotR (toR (Vero.sigma n u u')) (toR q) = 0 := by
    intro q hq
    have hq2 := (mem_Q2_iff n x y q).mp hq
    rw [V2R] at hq2
    refine dotR_eq_zero_of_mem_span (b := toR (Vero.sigma n u u')) ?_ (toR q) hq2
    rintro s (rfl | rfl)
    · exact hgen x hpx
    · exact hgen y hpy
  -- the pairing `⟨w, σ(u,u')⟩ = G²`
  have hpw : dotR (toR (Vero.sigma n u u'))
      (perpComp (Q2 n x y) (toR (veronese 2 n (x + y)))) = (G : ℝ) ^ 2 := by
    have hsum : (∑ i, (x + y) i * u i) = G := by
      rw [show (∑ i, (x + y) i * u i) = ∑ i, (x i * u i + y i * u i) from
        Finset.sum_congr rfl (fun i _ => by simp only [Pi.add_apply]; ring),
        Finset.sum_add_distrib, hσx, hσy, zero_add]
    have hsum' : (∑ i, (x + y) i * u' i) = G := by
      rw [show (∑ i, (x + y) i * u' i) = ∑ i, (x i * u' i + y i * u' i) from
        Finset.sum_congr rfl (fun i _ => by simp only [Pi.add_apply]; ring),
        Finset.sum_add_distrib, hσx', hσy', add_zero]
    have h1 : dotR (toR (Vero.sigma n u u')) (toR (veronese 2 n (x + y))) = (G : ℝ) ^ 2 := by
      rw [dotR_toR_sigma u u' (x + y), hsum, hsum']
      push_cast; ring
    have h2 : dotR (toR (Vero.sigma n u u'))
        (toR (veronese 2 n (x + y)) - perpComp (Q2 n x y) (toR (veronese 2 n (x + y)))) = 0 := by
      have hmem : toR (veronese 2 n (x + y)) - perpComp (Q2 n x y) (toR (veronese 2 n (x + y)))
          ∈ Submodule.span ℝ (intCastPi '' (Q2 n x y : Set (Mon 2 n → ℤ))) := hp1
      refine dotR_eq_zero_of_mem_span (b := toR (Vero.sigma n u u')) ?_ _ hmem
      rintro s ⟨q, hq, rfl⟩
      exact hnu_orthQ q hq
    have h3 : dotLin (toR (Vero.sigma n u u')) (toR (veronese 2 n (x + y)))
        = dotLin (toR (Vero.sigma n u u'))
            (toR (veronese 2 n (x + y)) - perpComp (Q2 n x y) (toR (veronese 2 n (x + y))))
          + dotLin (toR (Vero.sigma n u u'))
              (perpComp (Q2 n x y) (toR (veronese 2 n (x + y)))) := by
      rw [← map_add]
      congr 1
      abel
    simp only [dotLin_apply] at h3
    linarith [h1, h2]
  -- integrality: `γ * G^2 ∈ ℤ`
  have hint : γ * (G : ℝ) ^ 2 ∈ (Set.range (Int.cast : ℤ → ℝ) : Set ℝ) := by
    have hz : intCastPi (Vero.sigma n u u') ∈ realify (Gam 2 n x y) :=
      Submodule.mem_map_of_mem hnu_mem
    obtain ⟨k, hk⟩ := ha.2 (intCastPi (Vero.sigma n u u')) hz
    refine ⟨k, ?_⟩
    have h5 : ∑ i, a i * ((Vero.sigma n u u') i : ℝ) = γ * (G : ℝ) ^ 2 := by
      have e1 : (∑ i, a i * ((Vero.sigma n u u') i : ℝ))
          = dotR a (toR (Vero.sigma n u u')) := by rw [dotR_toR]
      rw [e1, ha', dotR_smul_left', dotR_comm', hpw]
    exact hk.symm.trans h5
  obtain ⟨k, hk⟩ := hint
  have hkne : k ≠ 0 := by
    intro h0
    refine hγne ?_
    have hk0 : γ * (G : ℝ) ^ 2 = 0 := by rw [← hk, h0]; simp
    exact (mul_eq_zero.mp hk0).resolve_right (pow_ne_zero 2 hGne)
  have hγge : 1 / (G : ℝ) ^ 2 ≤ |γ| := by
    have h1 : |γ| * (G : ℝ) ^ 2 = |(k : ℝ)| := by
      rw [hk]
      rw [abs_mul, abs_of_nonneg (show (0 : ℝ) ≤ (G : ℝ) ^ 2 by positivity)]
    have h2 : (1 : ℝ) ≤ |(k : ℝ)| := by
      rw [← Int.cast_abs]
      exact_mod_cast Int.one_le_abs hkne
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (G : ℝ) ^ 2), h1]
    exact h2
  -- norm computation and the two numeric bounds
  have hnorm : rNorm a
      = |γ| * rNorm (perpComp (Q2 n x y) (toR (veronese 2 n (x + y)))) := by
    rw [ha', rNorm_smul']
  have hwbound : (wedgeNorm x y) ^ 2
      ≤ 3 * (eNorm x * eNorm y) * rNorm (perpComp (Q2 n x y) (toR (veronese 2 n (x + y)))) :=
    PerpCompSigmaGe x y hxy
  have hxy_pos : 0 < eNorm x * eNorm y :=
    mul_pos (eNorm_pos_of_ne_zero (isPrim_ne_zero hx)) (eNorm_pos_of_ne_zero (isPrim_ne_zero hy))
  have hd2 : dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) ≤ wedgeNorm x y / (G : ℝ) := by
    rw [hG]; exact (DminPairLe x y hxy).1
  have hd2nonneg : 0 ≤ dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) := dmin_nonneg _ _
  have hd2sq : dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) ^ 2
      ≤ (wedgeNorm x y) ^ 2 / (G : ℝ) ^ 2 := by
    calc dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) ^ 2
        ≤ (wedgeNorm x y / (G : ℝ)) ^ 2 := pow_le_pow_left₀ hd2nonneg hd2 2
      _ = (wedgeNorm x y) ^ 2 / (G : ℝ) ^ 2 := by rw [div_pow]
  have hwd : (wedgeNorm x y) ^ 2 / (3 * (eNorm x * eNorm y))
      ≤ rNorm (perpComp (Q2 n x y) (toR (veronese 2 n (x + y)))) := by
    rw [div_le_iff₀ (by positivity)]
    linarith [hwbound]
  -- assembly
  calc (1 / 3) * (dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) ^ 2 / (eNorm x * eNorm y))
      ≤ (1 / 3) * ((wedgeNorm x y) ^ 2 / (G : ℝ) ^ 2 / (eNorm x * eNorm y)) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        rw [div_le_div_iff_of_pos_right hxy_pos]
        exact hd2sq
    _ = (1 / (G : ℝ) ^ 2) * ((wedgeNorm x y) ^ 2 / (3 * (eNorm x * eNorm y))) := by
        field_simp
    _ ≤ |γ| * rNorm (perpComp (Q2 n x y) (toR (veronese 2 n (x + y)))) :=
        mul_le_mul hγge hwd (by positivity) (abs_nonneg γ)
    _ = rNorm a := hnorm.symm

/-! ## The rank-two span lemma -/

/-- For a rank-two lattice `L ⊆ ℤ^ι` containing two `ℤ`-independent vectors `x, y`, the real span of
`L` is `span_ℝ{toR x, toR y}`. -/
lemma span_intCast_of_rank_two {ι : Type*} [Fintype ι] [DecidableEq ι] {L : Submodule ℤ (ι → ℤ)}
    {x y : ι → ℤ} (hrk : rk L = 2) (hx : x ∈ L) (hy : y ∈ L)
    (hind : LinearIndependent ℤ ![x, y]) :
    Submodule.span ℝ (intCastPi '' (L : Set (ι → ℤ)))
      = Submodule.span ℝ ({toR x, toR y} : Set (ι → ℝ)) := by
  have hle : Submodule.span ℝ ({toR x, toR y} : Set (ι → ℝ))
      ≤ Submodule.span ℝ (intCastPi '' (L : Set (ι → ℤ))) := by
    rw [Submodule.span_le]
    rintro s (rfl | rfl)
    · rw [toR_eq_intCastPi]
      exact Submodule.subset_span ⟨x, hx, rfl⟩
    · rw [toR_eq_intCastPi]
      exact Submodule.subset_span ⟨y, hy, rfl⟩
  have h1 : Module.finrank ℝ (Submodule.span ℝ (intCastPi '' (L : Set (ι → ℤ)))) = 2 := by
    rw [Work.HP.Vero.finrank_span_image_intCastPi]
    exact hrk
  have h2 : Module.finrank ℝ (Submodule.span ℝ ({toR x, toR y} : Set (ι → ℝ))) = 2 := by
    have hindR : LinearIndependent ℝ ![toR x, toR y] := by
      have h := Work.HP.Vero.linInd_intCastPi hind
      have h2 : (fun j : Fin 2 => intCastPi (![x, y] j)) = ![intCastPi x, intCastPi y] := by
        funext j
        fin_cases j <;> rfl
      rw [h2] at h
      simpa only [toR_eq_intCastPi] using h
    rw [show ({toR x, toR y} : Set (ι → ℝ)) = Set.range ![toR x, toR y] from by
      ext s
      constructor
      · rintro (rfl | rfl)
        · exact ⟨0, rfl⟩
        · exact ⟨1, rfl⟩
      · rintro ⟨i, rfl⟩
        fin_cases i <;> simp]
    rw [finrank_span_eq_card hindR, Fintype.card_fin]
  refine le_antisymm ?_ hle
  by_contra hne
  have hlt : Submodule.span ℝ ({toR x, toR y} : Set (ι → ℝ))
      < Submodule.span ℝ (intCastPi '' (L : Set (ι → ℤ))) :=
    lt_of_le_of_ne hle (fun h => hne (le_of_eq h.symm))
  have := Submodule.finrank_lt_finrank_of_lt hlt
  omega

/-! ## The second case of the dichotomy -/

/-- **Second case.** If a nonzero element `a` of the dual of `Γ = Λ_{ν₂(x)} ∩ Λ_{ν₂(y)}` does not lie
in `V₃ = span_ℝ{ν₂(x), ν₂(y), ν₂(x+y)}`, then `(1/3) 𝔡₃(x,y)/𝔡₂(x,y) ≤ ‖a‖`.

By the σ-witness (`RowWitness`) there are `i` and `v` with `⟨v,x⟩ = ⟨v,y⟩ = 0` and
`⟨rᵢ(a), v⟩ ≠ 0`; with `b ∈ ℤ^N` the integer representative of `a` modulo `V₂`
(`Vero.dualLat_int_shift`), the integer vector `rᵢ(b)` satisfies `rᵢ(b) - rᵢ(a) ∈ span_ℝ{x,y}`, hence
`rᵢ(b) ∉ span_ℝ(ℒ)` for every rank-two lattice `ℒ ⊇ ℤx ⊕ ℤy`.  For such `ℒ` the lattice
`ℒ ⊔ ℤrᵢ(b)` has rank three, contains `x` and `y`, and (covolume formula, `CovolumeSingle`) has
covolume `detL ℒ · ‖rᵢ(b)_⊥‖ ≤ detL ℒ · ‖a‖`; taking the infimum over `ℒ` gives
`𝔡₃ ≤ 𝔡₂ ‖a‖`. -/
theorem caseTwo {n : ℕ} (x y : Fin (n + 1) → ℤ) (hx : IsPrim x) (hy : IsPrim y)
    (hxy : LinearIndependent ℤ ![x, y]) (a : Mon 2 n → ℝ)
    (ha : a ∈ dualLat (realify (Gam 2 n x y))) (ha0 : a ≠ 0) (hV3 : a ∉ V3R n x y) :
    (1 / 3) * (dmin 3 ({x, y} : Set (Fin (n + 1) → ℤ))
        / dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ))) ≤ rNorm a := by
  classical
  -- the integer representative of `a` modulo `V₂`
  obtain ⟨b, lam, mu, hb⟩ := Vero.dualLat_int_shift x y hx hy hxy a ha
  -- the σ-witness
  obtain ⟨i, v, hvx, hvy, hv⟩ := RowWitness x y hxy a hV3
  set A : Fin (n + 1) → ℝ := rowVecR n i a with hA
  set Bz : Fin (n + 1) → ℤ := Vero.rowVec n i b with hBz
  have hB : rowVecR n i (toR b) = toR Bz := rfl
  have hAv : (∑ j, A j * v j) ≠ 0 := hv
  have hAne : A ≠ 0 := by
    intro h0
    refine hAv ?_
    rw [h0]
    simp
  -- `v` is orthogonal to `span_ℝ{toR x, toR y}`
  have hv_orth : ∀ w ∈ Submodule.span ℝ ({toR x, toR y} : Set (Fin (n + 1) → ℝ)),
      dotR w (toR v) = 0 := by
    have h := dotR_eq_zero_of_mem_span (b := toR v)
      (S := ({toR x, toR y} : Set (Fin (n + 1) → ℝ))) ?_
    · intro w hw
      rw [dotR_comm']
      exact h w hw
    rintro s (rfl | rfl)
    · rw [dotR_toR]
      simp only [toR]
      rw [show (∑ j, (v j : ℝ) * (x j : ℝ)) = ((∑ j, v j * x j : ℤ) : ℝ) from by
        push_cast
        rfl]
      rw [hvx]
      simp
    · rw [dotR_toR]
      simp only [toR]
      rw [show (∑ j, (v j : ℝ) * (y j : ℝ)) = ((∑ j, v j * y j : ℤ) : ℝ) from by
        push_cast
        rfl]
      rw [hvy]
      simp
  -- `A ∉ span_ℝ{toR x, toR y}`
  have hAnotspan : A ∉ Submodule.span ℝ ({toR x, toR y} : Set (Fin (n + 1) → ℝ)) := by
    intro hmem
    have h0 : (∑ j, A j * v j) = 0 := by
      have h := hv_orth A hmem
      rw [dotR_toR] at h
      rw [show (∑ j, A j * (v j : ℝ)) = (∑ j, A j * v j) from rfl]
      exact h
    exact hAv h0
  -- `toR Bz - A ∈ span_ℝ{toR x, toR y}`
  have hBA : toR Bz - A ∈ Submodule.span ℝ ({toR x, toR y} : Set (Fin (n + 1) → ℝ)) := by
    have hba : toR b - a = lam • toR (veronese 2 n x) + mu • toR (veronese 2 n y) := by
      ext m
      simpa only [toR, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul] using hb m
    have h1 : toR Bz - A = rowVecR n i (toR b - a) := by
      rw [← hB]
      rw [← rowVecR_sub]
    rw [h1, hba, rowVecR_add, rowVecR_smul, rowVecR_smul, rowVecR_veronese, rowVecR_veronese]
    have hx' : toR x ∈ Submodule.span ℝ ({toR x, toR y} : Set (Fin (n + 1) → ℝ)) :=
      Submodule.subset_span (Set.mem_insert _ _)
    have hy' : toR y ∈ Submodule.span ℝ ({toR x, toR y} : Set (Fin (n + 1) → ℝ)) :=
      Submodule.subset_span (Set.mem_insert_of_mem _ rfl)
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hx'))
      (Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hy'))
  have hApos : 0 < rNorm A := by
    obtain ⟨j, hj⟩ := Function.ne_iff.mp hAne
    have hpos : 0 < ∑ i, (A i) ^ 2 :=
      Finset.sum_pos' (fun i _ => sq_nonneg _) ⟨j, Finset.mem_univ j, sq_pos_of_ne_zero hj⟩
    exact Real.sqrt_pos_of_pos hpos
  have hle : dmin 3 ({x, y} : Set (Fin (n + 1) → ℤ)) / rNorm A
      ≤ dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) := by
    have hM0rk : rk (Submodule.span ℤ ({x, y} : Set (Fin (n + 1) → ℤ))) = 2 := by
      have hrange : (Set.range ![x, y]) = ({x, y} : Set (Fin (n + 1) → ℤ)) := by
        ext z
        constructor
        · rintro ⟨i, rfl⟩
          fin_cases i <;> simp
        · intro hz
          rcases hz with hz | hz
          · exact ⟨0, by simpa using hz.symm⟩
          · exact ⟨1, by simpa using hz.symm⟩
      rw [← hrange]
      show Module.finrank ℤ (Submodule.span ℤ (Set.range ![x, y])) = 2
      rw [finrank_span_eq_card hxy, Fintype.card_fin]
    rw [dmin]
    refine le_csInf ⟨detL (Submodule.span ℤ ({x, y} : Set (Fin (n + 1) → ℤ))),
      ⟨_, hM0rk, fun z hz => Submodule.subset_span hz, rfl⟩⟩ ?_
    rintro D ⟨L, hrk, hsub, rfl⟩
    -- the two facts about `perpComp` for the admissible lattice `L`
    have hLspan : Submodule.span ℝ ({toR x, toR y} : Set (Fin (n + 1) → ℝ))
        ≤ Submodule.span ℝ (intCastPi '' (L : Set (Fin (n + 1) → ℤ))) := by
      rw [Submodule.span_le]
      rintro s (rfl | rfl)
      · rw [toR_eq_intCastPi]
        exact Submodule.subset_span ⟨x, hsub (by simp), rfl⟩
      · rw [toR_eq_intCastPi]
        exact Submodule.subset_span ⟨y, hsub (by simp), rfl⟩
    have hcoset : toR Bz - A ∈ Submodule.span ℝ (intCastPi '' (L : Set (Fin (n + 1) → ℤ))) :=
      hLspan hBA
    have heq : perpComp L (toR Bz) = perpComp L A :=
      (PerpCompLemmas L (toR Bz) A hcoset).2.2.2.2.1
    have hperP : perpComp L (toR Bz) ≠ 0 := by
      intro h0
      have hA0 : perpComp L A = 0 := by rw [← heq]; exact h0
      have hAi := (PerpCompLemmas L A A (by simp)).1
      rw [hA0, sub_zero] at hAi
      have hST := span_intCast_of_rank_two hrk (hsub (by simp)) (hsub (by simp)) hxy
      exact hAnotspan (hST ▸ hAi)
    obtain ⟨hrk3, hdet⟩ := CovolumeSingle L Bz hperP
    have hnorm : rNorm (perpComp L (toR Bz)) ≤ rNorm A := by
      rw [heq]
      exact (PerpCompLemmas L A A (by simp)).2.2.2.2.2.1
    have hd3le : dmin 3 ({x, y} : Set (Fin (n + 1) → ℤ))
        ≤ detL (L ⊔ Submodule.span ℤ ({Bz} : Set (Fin (n + 1) → ℤ))) := by
      refine dmin_le_detL (r := 3) (by rw [hrk3, hrk]) ?_
      rintro z (rfl | rfl)
      · exact Submodule.mem_sup_left (hsub (by simp))
      · exact Submodule.mem_sup_left (hsub (by simp))
    rw [div_le_iff₀ hApos]
    calc dmin 3 ({x, y} : Set (Fin (n + 1) → ℤ))
        ≤ detL (L ⊔ Submodule.span ℤ ({Bz} : Set (Fin (n + 1) → ℤ))) := hd3le
      _ = detL L * rNorm (perpComp L (toR Bz)) := hdet
      _ ≤ detL L * rNorm A := mul_le_mul_of_nonneg_left hnorm (detL_nonneg L)
  have hAr : rNorm A ≤ rNorm a := by
    rw [hA]
    exact rNorm_rowVecR_le n i a
  have hle' : dmin 3 ({x, y} : Set (Fin (n + 1) → ℤ))
      ≤ dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) * rNorm A := (div_le_iff₀ hApos).mp hle
  have h2 : dmin 3 ({x, y} : Set (Fin (n + 1) → ℤ))
      ≤ dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) * rNorm a :=
    le_trans hle' (mul_le_mul_of_nonneg_left hAr (dmin_nonneg 2 _))
  rcases eq_or_lt_of_le (dmin_nonneg (2 : ℕ) ({x, y} : Set (Fin (n + 1) → ℤ))) with h0 | h0
  · rw [← h0, div_zero, mul_zero]
    exact Vero.rNorm_nonneg' a
  · have h3 : dmin 3 ({x, y} : Set (Fin (n + 1) → ℤ))
        / dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) ≤ rNorm a := by
      rw [div_le_iff₀ h0]
      calc dmin 3 ({x, y} : Set (Fin (n + 1) → ℤ))
          ≤ dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) * rNorm a := h2
        _ = rNorm a * dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) := mul_comm _ _
    calc (1 / 3) * (dmin 3 ({x, y} : Set (Fin (n + 1) → ℤ))
          / dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)))
        ≤ (1 / 3) * rNorm a := mul_le_mul_of_nonneg_left h3 (by norm_num)
      _ ≤ rNorm a := by linarith [Vero.rNorm_nonneg' a]

/-- For `n ≥ 2` and primitive, `ℤ`-linearly independent `x, y ∈ ℤ^{n+1}`, the first successive
minimum of the lattice dual to `Gam 2 n x y` is at least `(1/3)·min{𝔡₃/𝔡₂, 𝔡₂²/(‖x‖‖y‖)}`, where
`𝔡_r = dmin r {x,y}` and `dualLat`/`lamR`/`realify` are as in `Submission/Work/HP/Vero.lean`.
This is the combination of the paper's "Lower bound first case" and "Lower bound second case"
(Browning–Le Boudec–Sawin §3.3, `d = 2`); a detailed proof sketch is in
`Submission/Work/HP/Vero/lamR_dual_Gam_two.lean`. -/
theorem GamTwo_dual_lam1 (n : ℕ) (hn : 2 ≤ n) (x y : Fin (n + 1) → ℤ) (hx : IsPrim x)
    (hy : IsPrim y) (hxy : LinearIndependent ℤ ![x, y]) :
    (1 / 3) * min (dmin 3 {x, y} / dmin 2 {x, y}) (dmin 2 {x, y} ^ 2 / (eNorm x * eNorm y))
      ≤ lamR (dualLat (realify (Gam 2 n x y))) 1 := by
  obtain ⟨a₀, ha₀, ha₀ne⟩ := Vero.dualLat_nonempty hn x y hx hy hxy
  refine Vero.le_lamR_one _ ⟨a₀, ha₀, ha₀ne⟩ ?_
  intro a ha ha0
  by_cases hcase : a ∈ V3R n x y
  · have h1 := caseOne x y hx hy hxy a ha ha0 hcase
    calc (1 / 3) * min (dmin 3 {x, y} / dmin 2 {x, y})
            (dmin 2 {x, y} ^ 2 / (eNorm x * eNorm y))
        ≤ (1 / 3) * (dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ)) ^ 2 / (eNorm x * eNorm y)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact min_le_right _ _
      _ ≤ rNorm a := h1
  · have h2 := caseTwo x y hx hy hxy a ha ha0 hcase
    calc (1 / 3) * min (dmin 3 {x, y} / dmin 2 {x, y})
            (dmin 2 {x, y} ^ 2 / (eNorm x * eNorm y))
        ≤ (1 / 3) * (dmin 3 ({x, y} : Set (Fin (n + 1) → ℤ))
            / dmin 2 ({x, y} : Set (Fin (n + 1) → ℤ))) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact min_le_left _ _
      _ ≤ rNorm a := h2


end Work.HP.Sig2
