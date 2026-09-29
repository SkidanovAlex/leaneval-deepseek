import Mathlib
import Submission.Work.Cert.Spec
import Submission.Work.Haupt.haupt_facts

/-! Guidance from the project lead (the requester):

Context (from the project lead). Theorem A, ANumerics conjunct 2 (rearrangement integral ≤ 11.2) and the
outer winding of φ_A + 1/72 are certified by a LEAD-BUILT integer certificate ("verify, don't compute"):
`Submission/Work/Cert/Defs.lean` (checker `leafOK`, scale `S = 2^40·10^8`, `fdiv = Int.ediv`, `md` = floor
product, `mu` = ceil product, `dvu` = ceil quotient), `WindDefs.lean` (`qChain`, `gDisc`, `windLeafOK`,
`labelsOK`), 15,511 conjunct-2 leaves in `Chunks/C000..C155` (each `okC### : arcsOK … = true` by
`decide +kernel`, linked in `Final.lean`: `link_ok`, `first_ok`, `total_ok`, `vals_length`), 4,553 winding
leaves in `WChunks/W000..W045` (`WindFinal.lean`: `wlink_ok`, `wfirst_ok`, `wj_ok`, `wlabels_ok`), and
`SrCheck.lean` (`sr_all`, `wsr_all`). The contracts are the `Prop`s in `Submission/Work/Cert/Spec.lean`
(read it first). DO NOT build kernel chains / evaluate numerics in the kernel yourself and do not edit
Defs/WindDefs/Spec/chunks: your job is the real-analysis soundness of the integer operations. Reuse
proved lemmas: APsi `slit_facts`/`differentiableOn_slit`/`slit_norm_lt_one`/`lune_norm_bounds`,
ANum3 `slitM2B_sound`, `luneM2B_sound`, `luneM2B_numeric_core`, `norm_deriv_sub_le_of_ball`,
`norm_rot_sub_le`, `hauptH_norm_le_exp`, `hTailC_le`, `sqrtJS_mem`/`slitEnclJS_mem`/`luneEnclJS_mem`
(same ideas, older interval types), `phiA_analytic_ext`, `psiA_facts`, `haupt_facts`. No native_decide.
Rounding facts you will need repeatedly: `Int.ediv` with positive divisor is floor
(`Int.ediv_mul_le`, `Int.lt_ediv_add_one_mul_self`); prove small helper lemmas for md/mu/dvu once.

Jacobi: with q = e^{iπτ}, λ(τ) = θ₂⁴/θ₃⁴ and 1 − λ = θ₄⁴/θ₃⁴; hauptH(q) = −256 q ∏(1+q^n)^24 equals
−16 λ(τ)/(1 − λ(τ))² ... in the form needed: hauptH(q)·θ₄(q)^8 = −256 q A(q)^8 where θ₄ = thetaB and
A(q) = Σ q^{n(n+1)/2} = ∏(1−q^{2n})(1+q^n)² ... use the Jacobi triple product (Mathlib:
`jacobiTheta₂_term`, `JacobiTheta.triple_product`? check `Mathlib/NumberTheory/ModularForms/JacobiTheta/`),
giving A(q) = ∏_{n≥1}(1 − q^{2n})(1 + q^n)^2 ·(1/ (1+q^0))... precisely Gauss: Σ q^{n(n+1)/2} = ∏ (1−q^{2n})/(1−q^{2n−1}),
θ₄(q) = ∏ (1−q^{2n})(1−q^{2n−1})². Then A^8/θ₄^8 = ∏ 1/((1−q^{2n−1})^{24}) = ∏ (1+q^n)^{24} by Euler
(∏(1+q^n)·∏(1−q^{2n−1}) = 1). Agent H4 proved theta-product lemmas for Theorem C (Work.Haupt / ZeroEst) —
search them first. Numerically verified: q = 0.5+0.3i gives both sides 4585.2511+17.2340i.
-/

namespace Work.Cert

open Work.Haupt

/-! ## Reduction of `ThetaIdentity` to the theta series of `Work.Haupt`

`ThetaIdentity` states `h(q)·θ₄(q)^8 = -256·q·A(q)^8` for `‖q‖ < 1`, where
`h = hauptH`, `θ₄ = thetaB` and `A = thetaA`.  The two series `thetaA`, `thetaB` are the
*naive* `ℕ`-indexed Jacobi–Gauss series of `Submission/Work/Cert/Spec.lean`, while the
established Area-M theory (`Submission/Work/Haupt`) works with the `ℤ`-indexed series
`T2 x = ∑'_{n∈ℤ} x^{n(n+1)}` (⧸ the odd part of `θ₂`) and `T4 x = ∑'_{n∈ℤ} (-1)^n x^{n²} = θ₄(x)`.

The dictionary proved here is

* `thetaB_eq_T4  : thetaB q = T4 q` (symmetry of the `ℤ`-sum and `(-1)^{-k} = (-1)^k`);
* `T2_eq_two_mul_thetaA : T2 x = 2 · thetaA (x^2)` (the involution `n ↦ -n-1` on `ℤ` and
  `2 ∣ n(n+1)`).

With these, `hauptH_mul_T4_of` (Area M) at `x = sqrt q` is *exactly* the desired identity.
-/

/-- `(-1) ^ (-(n+1)) = (-1) ^ (n+1)` for the `ℤ`-power on `ℂ`. -/
lemma negOne_zpow_neg_add_one (n : ℕ) :
    (-1 : ℂ) ^ (-((n : ℤ) + 1)) = (-1 : ℂ) ^ ((n : ℤ) + 1) := by
  have h : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
  rw [← h, zpow_neg, zpow_natCast, Work.Haupt.inv_neg_one_pow]

/-- The summand of `T4 q` at the negative index `-(n+1)` is the summand of the `ℕ`-series
`∑'_{n≥0} (-1)^{n+1} q^{(n+1)²}` used in `thetaB`. -/
lemma negOne_q_pow_neg (q : ℂ) (n : ℕ) :
    (-1 : ℂ) ^ (-((n : ℤ) + 1)) * q ^ ((-((n : ℤ) + 1)) ^ 2)
      = (-1 : ℂ) ^ (n + 1) * q ^ ((n + 1) ^ 2) := by
  rw [negOne_zpow_neg_add_one n]
  have h : ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 := by push_cast; ring
  have h2 : (-((n : ℤ) + 1)) ^ 2 = (((n + 1) ^ 2 : ℕ) : ℤ) := by push_cast; ring
  rw [h2, ← h, zpow_natCast, zpow_natCast]

/-- `thetaB` is the `ℤ`-indexed theta constant `θ₄ = T4`. -/
theorem thetaB_eq_T4 (q : ℂ) (hq : ‖q‖ < 1) : thetaB q = T4 q := by
  set f : ℤ → ℂ := fun n => (-1 : ℂ) ^ n * q ^ (n ^ 2) with hf
  have hnorm : Summable (fun n : ℤ => ‖f n‖) := by
    rw [hf]; exact summable_norm_pow_sq_mul q hq
  have hs : Summable f := Summable.of_norm hnorm
  have hs1 : Summable (fun n : ℕ => f n) := hs.comp_injective (fun a b h => Int.ofNat.inj h)
  have hneg : Function.Injective (fun n : ℕ => -((n : ℤ) + 1)) := by
    intro a b h; simp only at h; omega
  have hs2 : Summable (fun n : ℕ => f (-((n : ℤ) + 1))) := hs.comp_injective hneg
  -- the positive tail is `f 0` plus the negative tail
  have hpt1 : ∀ n : ℕ, f (((n + 1 : ℕ)) : ℤ) = f (-((n : ℤ) + 1)) := by
    intro n
    simp only [hf]
    rw [show (((n + 1 : ℕ)) : ℤ) = (n : ℤ) + 1 from by push_cast; ring]
    rw [← negOne_zpow_neg_add_one n]
    congr 1
  -- the negative tail is the `thetaB` sum
  have hpt2 : ∀ n : ℕ, f (-((n : ℤ) + 1)) = (-1 : ℂ) ^ (n + 1) * q ^ ((n + 1) ^ 2) := by
    intro n
    simp only [hf]
    exact negOne_q_pow_neg q n
  have hmain : T4 q = 1 + 2 * (∑' n : ℕ, (-1 : ℂ) ^ (n + 1) * q ^ ((n + 1) ^ 2)) := by
    show (∑' n : ℤ, f n) = _
    have hf0 : f (0 : ℤ) = 1 := by simp [hf]
    rw [tsum_of_nat_of_neg_add_one hs1 hs2]
    rw [hs1.tsum_eq_zero_add]
    rw [show f (((0 : ℕ)) : ℤ) = 1 from hf0]
    rw [tsum_congr hpt1]
    rw [tsum_congr hpt2]
    ring
  simp only [thetaB]
  exact hmain.symm

/-- `thetaA (x²)` is half of the `ℤ`-indexed series `T2 x`. -/
theorem T2_eq_two_mul_thetaA (x : ℂ) (hx : ‖x‖ < 1) : T2 x = 2 * thetaA (x ^ 2) := by
  set f : ℤ → ℂ := fun n => x ^ (n * (n + 1)) with hf
  have hnorm : Summable (fun n : ℤ => ‖f n‖) := by
    rw [hf]; exact summable_norm_pow_mul_succ x hx
  have hs : Summable f := Summable.of_norm hnorm
  have hs1 : Summable (fun n : ℕ => f n) := hs.comp_injective (fun a b h => Int.ofNat.inj h)
  have hneg : Function.Injective (fun n : ℕ => -((n : ℤ) + 1)) := by
    intro a b h; simp only at h; omega
  have hs2 : Summable (fun n : ℕ => f (-((n : ℤ) + 1))) := hs.comp_injective hneg
  -- the involution `n ↦ -(n+1)` fixes the summand `x^{n(n+1)}`
  have hsymm : ∀ n : ℕ, f (-((n : ℤ) + 1)) = f ((n : ℤ)) := by
    intro n
    simp only [hf]
    congr 1
    ring
  -- the positive tail is `thetaA (x²)`
  have hcauchy : ∀ n : ℕ, f ((n : ℤ)) = (x ^ 2) ^ (n * (n + 1) / 2) := by
    intro n
    simp only [hf]
    have h1 : ((n : ℤ)) * ((n : ℤ) + 1) = ((n * (n + 1) : ℕ) : ℤ) := by push_cast; ring
    rw [h1, zpow_natCast]
    have h2 : n * (n + 1) = 2 * (n * (n + 1) / 2) := by
      have hd : 2 ∣ n * (n + 1) := even_iff_two_dvd.mp (Nat.even_mul_succ_self n)
      exact (Nat.mul_div_cancel' hd).symm
    conv_lhs => rw [h2]
    rw [pow_mul]
  rw [T2, thetaA]
  show (∑' n : ℤ, f n) = 2 * ∑' n : ℕ, (x ^ 2) ^ (n * (n + 1) / 2)
  rw [tsum_of_nat_of_neg_add_one hs1 hs2]
  rw [tsum_congr hsymm]
  rw [tsum_congr hcauchy]
  ring

theorem theta_identity : ThetaIdentity := by
  intro q hq
  have hx : ‖Complex.sqrt q‖ < 1 := Work.Haupt.sqrt_norm_lt_one q hq
  -- Area M: `hauptH (x²) θ₄(x²)^8 = -x² θ₂-part(x)^8`
  have hmain := hauptH_mul_T4_of theta_four_product theta_two_product (Complex.sqrt q) hx
  rw [Work.Haupt.sqrt_sq] at hmain
  rw [thetaB_eq_T4 q hq]
  rw [hmain, T2_eq_two_mul_thetaA (Complex.sqrt q) hx, Work.Haupt.sqrt_sq]
  ring

end Work.Cert
