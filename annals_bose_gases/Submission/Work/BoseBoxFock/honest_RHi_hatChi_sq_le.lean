import ChallengeDeps
import Mathlib.Data.ZMod.ValMinAbs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBoxFock.AllDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.honest_RHi_hatChi_sq_le`

**The high-momentum `χ̂`-tail of the honest box environment.**

The environment's `χ̂`-kernel is `E.hatChi k = χ̂_ℓ(kmom k)/χ̂²_ℓ(0)`, which for the honest
model equals the *corpus* `χ̂` at the lattice momentum `vec (labVec N k)` (`Clean.honest_hatChi_eq`).
FS `lem:DecaychiHat` (`ChiReg corpusBox 26 Cchi`) bounds this by `Cchi (1+‖p‖²)^{-26}`.

The high-momentum region `RHi` is `‖kmom k‖ ≥ K_L√(μa)/2`, i.e. `‖vec (labVec N k)‖ ≥ R` with

    R = ℓ · K_L · √(μa)/2,      ℓ = sideAt μ (a v),   K_L = (K_ℓ d²)^{-1},

and since `ℓ√(μa) = K_ℓ` this collapses to `R = 1/(2d²) = (fsX v μ)^{-12}/2` (pure powers of
`fsX`).  The lattice tail bound `Work.BoseK15.sum_inv_one_add_norm_tail` (dyadic annuli, sharp
constant `128`) then gives

    ∑_{RHi} χ̂_k² ≤ Cchi² · 128/R^101 = 128·Cchi²·2^101·(fsX v μ)^1212,

the exponent `1212 = 12·101 = 2·M̃·101` being the product of the decay order and the tail
exponent.  The hypothesis `hR1 : 1 ≤ (fsX v μ)^{-12}/2` is exactly the `1 ≤ R` that the dyadic
bound needs.
-/

noncomputable section

namespace Work.BoseBoxFock

/-! ## 1. The lattice label map is injective -/

/-- `labVec N` is injective: the least-absolute-value representative of `ZMod (2N+1)` is. -/
lemma honestRHi_labVec_inj (N : ℕ) (a b : Lab N) (hab : labVec N a = labVec N b) : a = b :=
  funext fun i => ZMod.injective_valMinAbs (congrFun hab i)

/-! ## 2. The `RHi` threshold is exactly `(fsX v μ)^{-12}/2` -/

/-- **The value of the high-momentum threshold.**  With `ℓ = sideAt μ (a v)` and
`K_L = (K_ℓ d²)^{-1} = ((paramsAt μ (a v)).Kl * (paramsAt μ (a v)).d ^ 2)^{-1}`,

    ℓ · (K_L · √(μ a)) / 2 = (fsX v μ)^{-12}/2.

(`ℓ√(μa) = K_ℓ = fsX^{-3/2}`, `K_ℓd² = fsX^{21/2}`, and `fsX = fsXp (dil v μ) 1`.) -/
lemma honestRHi_R_eq {v : ℝ³ → ℝ} {μ : ℝ} (hμ : 0 < μ)
    (hav : 0 < _root_.BoseGases.a v) :
    Work.BoseBox.sideAt μ (_root_.BoseGases.a v) *
      (((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
          * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d ^ 2) ^ (-(1 : ℝ))
        * Real.sqrt (μ * _root_.BoseGases.a v) / 2)
      = (Work.BoseFixR.fsX v μ) ^ (-(12 : ℝ)) / 2 := by
  have ht : 0 < Work.BoseFixR.dil v μ := by
    rw [Work.BoseFixR.dil]; positivity
  have hma : 0 < μ * _root_.BoseGases.a v := mul_pos hμ hav
  have hKl : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
      = Work.BoseBox.fsXp (Work.BoseFixR.dil v μ) 1 ^ (-(3 / 2 : ℝ)) := by
    show Work.BoseBox.fsXp (Work.BoseFixR.dil v μ) (-(3 / 2 : ℝ))
      = Work.BoseBox.fsXp (Work.BoseFixR.dil v μ) 1 ^ (-(3 / 2 : ℝ))
    rw [Work.BoseBox.fsXp_rpow ht.le]
    congr 1; ring
  have hd : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
      = Work.BoseBox.fsXp (Work.BoseFixR.dil v μ) 1 ^ 6 := by
    show Work.BoseBox.fsXp (Work.BoseFixR.dil v μ) 6
      = Work.BoseBox.fsXp (Work.BoseFixR.dil v μ) 1 ^ 6
    rw [Work.BoseBox.fsXp_pow ht.le]
    congr 1; norm_num
  have hX : Work.BoseFixR.fsX v μ
      = Work.BoseBox.fsXp (Work.BoseFixR.dil v μ) 1 := rfl
  have hsa : Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
      = Work.BoseBox.fsXp (Work.BoseFixR.dil v μ) 1 ^ (-(3 / 2 : ℝ))
          * (μ * _root_.BoseGases.a v) ^ (-(1 / 2 : ℝ)) := by
    rw [show Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
        = (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
            * (μ * _root_.BoseGases.a v) ^ (-(1 / 2 : ℝ)) from rfl, hKl]
  rw [hsa, hKl, hd, hX, Real.sqrt_eq_rpow]
  set u := Work.BoseBox.fsXp (Work.BoseFixR.dil v μ) 1 with hudef
  have hu : 0 < u := by rw [hudef]; exact Work.BoseBox.fsXp_pos ht
  have h1 : (u ^ (-(3 / 2 : ℝ)) * (u ^ 6) ^ 2) ^ (-(1 : ℝ)) = u ^ (-(21 / 2 : ℝ)) := by
    have hh : u ^ (-(3 / 2 : ℝ)) * (u ^ 6) ^ 2 = u ^ ((21 / 2 : ℝ)) := by
      rw [← pow_mul, show (6 * 2 : ℕ) = 12 by norm_num, ← Real.rpow_natCast u 12,
        ← Real.rpow_add hu]
      congr 1
      norm_num
    rw [hh, ← Real.rpow_mul hu.le]
    congr 1; norm_num
  have h2 : (μ * _root_.BoseGases.a v) ^ (-(1 / 2 : ℝ))
      * (μ * _root_.BoseGases.a v) ^ (1 / 2 : ℝ) = 1 := by
    rw [← Real.rpow_add hma, neg_add_cancel, Real.rpow_zero]
  have h3 : u ^ (-(3 / 2 : ℝ)) * u ^ (-(21 / 2 : ℝ)) = u ^ (-(12 : ℝ)) := by
    rw [← Real.rpow_add hu]; congr 1; norm_num
  rw [h1]
  rw [show u ^ (-(3 / 2 : ℝ)) * (μ * _root_.BoseGases.a v) ^ (-(1 / 2 : ℝ)) *
        (u ^ (-(21 / 2 : ℝ)) * (μ * _root_.BoseGases.a v) ^ (1 / 2 : ℝ) / 2)
      = u ^ (-(3 / 2 : ℝ)) * u ^ (-(21 / 2 : ℝ)) *
        ((μ * _root_.BoseGases.a v) ^ (-(1 / 2 : ℝ))
          * (μ * _root_.BoseGases.a v) ^ (1 / 2 : ℝ)) / 2 by ring]
  rw [h2, h3]; norm_num

/-- **`RHi` gives the threshold bound on the lattice momentum.**  If `k` is in the high-momentum
region of the honest environment at density `ρ`, then the lattice vector `vec (labVec N k)`
has length at least `ℓ · (K_L√(μa)/2) = (fsX v μ)^{-12}/2`. -/
lemma honestRHi_le_norm {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut} {HM : ∀ μ : ℝ, HonestModes v μ}
    {μ ρ : ℝ} (hμ : 0 < μ) (hav : 0 < _root_.BoseGases.a v)
    (k : Lab (HM μ).N)
    (hk : RHi (HonestBoxFam v h fc fu HM μ).F
        (Work.BoseFixR.KzEnvAt (HonestBoxFam v h fc fu HM μ).E ρ) k) :
    Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
      * (((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
            * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d ^ 2) ^ (-(1 : ℝ))
          * Real.sqrt (μ * _root_.BoseGases.a v) / 2)
      ≤ ‖Work.BoseB4.vec (labVec (HM μ).N k)‖ := by
  have hside : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) :=
    Work.BoseBox.sideAt_pos hμ hav
  have hell : ellH v μ = Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := by
    rw [ellH, if_pos hside]
  have hk' : ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d ^ 2) ^ (-(1 : ℝ))
        * Real.sqrt (μ * _root_.BoseGases.a v) / 2
      ≤ ‖kmomLab (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) (HM μ).N k‖ := by
    rw [← hell]
    exact hk
  have hsmul := congrArg (fun x : ℝ³ => ‖x‖)
    (smul_kmomLab (ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (ne_of_gt hside) (HM μ).N k)
  rw [norm_smul, Real.norm_of_nonneg hside.le] at hsmul
  calc Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
        * (((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
            * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d ^ 2) ^ (-(1 : ℝ))
          * Real.sqrt (μ * _root_.BoseGases.a v) / 2)
      ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
          * ‖kmomLab (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) (HM μ).N k‖ :=
        mul_le_mul_of_nonneg_left hk' hside.le
    _ = ‖Work.BoseB4.vec (labVec (HM μ).N k)‖ := hsmul

/-! ## 3. The dyadic tail bound at decay order `52` and tail exponent `101` -/

/-- **The lattice tail sum.**  A finite set of integer vectors all lying outside the ball of
radius `R ≥ 1` contributes at most `128/R^101` to the sum of `(1+‖vec n‖²)^{-52}`.

This is `Work.BoseK15.sum_inv_one_add_norm_tail` at `s = 52`, `M = 101 = 2·52 - 3` with the
constant `128` exposed (the `∃ C`-form of the library lemma hides it). -/
lemma honestRHi_sum_tail (R : ℝ) (S : Finset (Fin 3 → ℤ)) (hR : 1 ≤ R)
    (hS : ∀ n ∈ S, R ≤ ‖Work.BoseB4.vec n‖) :
    ∑ n ∈ S, (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52)⁻¹ ≤ 128 / R ^ 101 := by
  obtain ⟨K, hK⟩ := Work.BoseK15.exists_pow_mul_gt_norm R hR S
  refine le_trans (Work.BoseK15.sum_le_sum_annuli 52 K R S hR hS hK) ?_
  refine le_trans (Finset.sum_le_sum
    (fun k _ => Work.BoseK15.annulus_sum_bound 52 k R _ hR ?_ ?_)) ?_
  · intro n hn
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hn).1).2
  · intro n hn
    exact le_of_lt (lt_of_not_ge (Finset.mem_filter.mp hn).2)
  · have h := Work.BoseK15.annulus_terms_sum_bound 52 (K + 1) R hR (by norm_num : 2 ≤ 52)
    simpa using h

/-! ## 4. The final scalar arithmetic -/

/-- **The bookkeeping.**  For `X > 0` and `R = X^{-12}/2`,
`Cchi²·128/R^101 = 128·Cchi²·2^101·X^1212`. -/
lemma honestRHi_arith {X R Cchi : ℝ} (hX : 0 < X) (hR : R = X ^ (-(12 : ℝ)) / 2) :
    Cchi ^ 2 * (128 / R ^ 101) = (128 * Cchi ^ 2 * 2 ^ 101) * X ^ 1212 := by
  have hR101 : R ^ 101 = X ^ (-(1212 : ℝ)) / 2 ^ 101 := by
    rw [hR, div_pow]
    congr 1
    rw [← Real.rpow_natCast (X ^ (-(12 : ℝ))) 101, ← Real.rpow_mul hX.le]
    congr 1; norm_num
  rw [hR101]
  have hXinv : (X ^ (-(1212 : ℝ)))⁻¹ = X ^ 1212 := by
    rw [← Real.rpow_neg hX.le, neg_neg,
      show (1212 : ℝ) = ((1212 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  rw [div_div_eq_mul_div, div_eq_mul_inv, hXinv]
  ring

/-! ## 5. The theorem -/

theorem honest_RHi_hatChi_sq_le {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v}
    {fc fu : Work.BoseBoxFix.LowCut}
    {HM : ∀ μ : ℝ, Work.BoseBoxFock.HonestModes v μ} {μ ρ Cchi : ℝ}
    (hμ : 0 < μ) (hav : 0 < _root_.BoseGases.a v)
    (hChi : Work.BoseK15.ChiReg Work.BoseK15.corpusBox 26 Cchi) (hCchi : 0 ≤ Cchi)
    (hR1 : 1 ≤ (Work.BoseFixR.fsX v μ) ^ (-(12 : ℝ)) / 2)
    (hview : (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).viewFSAll v h μ) :
    (∑ k ∈ Finset.univ.filter (Work.BoseBoxFock.RHi
        (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F
        (Work.BoseFixR.KzEnvAt (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ)),
        ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.hatChi k) ^ 2)
      ≤ (128 * Cchi ^ 2 * 2 ^ 101) * (Work.BoseFixR.fsX v μ) ^ 1212 := by
  classical
  have hside : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) :=
    Work.BoseBox.sideAt_pos hμ hav
  have hterm : ∀ n : Fin 3 → ℤ,
      (Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec n)) ^ 2
        ≤ Cchi ^ 2 * (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52)⁻¹ := by
    intro n
    have hb : 0 < (1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 26 := by positivity
    have h1 : |Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec n)|
        ≤ Cchi / (1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 26 :=
      (le_div_iff₀ hb).mpr (hChi.1 (Work.BoseB4.vec n))
    calc (Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec n)) ^ 2
        = |Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec n)| ^ 2 := (sq_abs _).symm
      _ ≤ (Cchi / (1 + ‖Work.BoseB4.vec n‖ ^ 2) ^ 26) ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) h1 2
      _ = Cchi ^ 2 * (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52)⁻¹ := by
          rw [div_pow, div_eq_mul_inv]
          congr 1
          rw [← pow_mul, show (26 * 2 : ℕ) = 52 by norm_num]
  have hXpos : 0 < Work.BoseFixR.fsX v μ := by
    show 0 < Work.BoseBox.fsXp (Work.BoseFixR.dil v μ) 1
    exact Work.BoseBox.fsXp_pos (by rw [Work.BoseFixR.dil]; positivity)
  set R : ℝ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
      * (((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
            * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d ^ 2) ^ (-(1 : ℝ))
          * Real.sqrt (μ * _root_.BoseGases.a v) / 2) with hRdef
  have hRval : R = (Work.BoseFixR.fsX v μ) ^ (-(12 : ℝ)) / 2 := by
    rw [hRdef]; exact honestRHi_R_eq hμ hav
  have hR1' : 1 ≤ R := by rw [hRval]; exact hR1
  set S : Finset (Fin 3 → ℤ) :=
    (Finset.univ.filter (Work.BoseBoxFock.RHi
        (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F
        (Work.BoseFixR.KzEnvAt (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ))).image
      (Work.BoseBoxFock.labVec (HM μ).N) with hSdef
  have hSprop : ∀ n ∈ S, R ≤ ‖Work.BoseB4.vec n‖ := by
    intro n hn
    rw [hSdef] at hn
    obtain ⟨k, hk, hkn⟩ := Finset.mem_image.mp hn
    rw [← hkn, hRdef]
    exact honestRHi_le_norm hμ hav k ((Finset.mem_filter (p := Work.BoseBoxFock.RHi
      (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F
      (Work.BoseFixR.KzEnvAt (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ))).mp hk).2
  have hsum_eq : (∑ k ∈ Finset.univ.filter (Work.BoseBoxFock.RHi
          (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F
          (Work.BoseFixR.KzEnvAt (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ)),
          (Work.BoseK15.corpusBox.hatChi
            (Work.BoseB4.vec (Work.BoseBoxFock.labVec (HM μ).N k))) ^ 2)
      = ∑ n ∈ S, (Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec n)) ^ 2 := by
    rw [hSdef]
    exact (Finset.sum_image (s := Finset.univ.filter (Work.BoseBoxFock.RHi
          (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F
          (Work.BoseFixR.KzEnvAt (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ)))
        (f := fun n => (Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec n)) ^ 2)
        (g := Work.BoseBoxFock.labVec (HM μ).N)
        (fun x _ y _ hxy => honestRHi_labVec_inj (HM μ).N x y hxy)).symm
  calc (∑ k ∈ Finset.univ.filter (Work.BoseBoxFock.RHi
        (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F
        (Work.BoseFixR.KzEnvAt (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ)),
        ((Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E.hatChi k) ^ 2)
      = ∑ k ∈ Finset.univ.filter (Work.BoseBoxFock.RHi
          (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).F
          (Work.BoseFixR.KzEnvAt (Work.BoseBoxFock.HonestBoxFam v h fc fu HM μ).E ρ)),
          (Work.BoseK15.corpusBox.hatChi
            (Work.BoseB4.vec (Work.BoseBoxFock.labVec (HM μ).N k))) ^ 2 :=
        Finset.sum_congr rfl (fun k _ => by
          rw [Work.BoseBoxFock.Clean.honest_hatChi_eq v h fc fu HM μ hside k])
    _ = ∑ n ∈ S, (Work.BoseK15.corpusBox.hatChi (Work.BoseB4.vec n)) ^ 2 := hsum_eq
    _ ≤ ∑ n ∈ S, Cchi ^ 2 * (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52)⁻¹ :=
        Finset.sum_le_sum (fun n _ => hterm n)
    _ = Cchi ^ 2 * ∑ n ∈ S, (((1 : ℝ) + ‖Work.BoseB4.vec n‖ ^ 2) ^ 52)⁻¹ := by
        rw [Finset.mul_sum]
    _ ≤ Cchi ^ 2 * (128 / R ^ 101) :=
        mul_le_mul_of_nonneg_left (honestRHi_sum_tail R S hR1' hSprop) (sq_nonneg Cchi)
    _ = (128 * Cchi ^ 2 * 2 ^ 101) * (Work.BoseFixR.fsX v μ) ^ 1212 :=
        honestRHi_arith hXpos hRval

end Work.BoseBoxFock
