import Mathlib
import Submission.Work.Diff.STE.B3.VarCoef.Defs
import Submission.Work.Diff.STE.B3.SymCalcStep8.CSqZ
import Submission.Work.Diff.STE.B3.VarCoef.OpOrder
import Submission.Work.Diff.STE.B3.VarCoef.Assembly
import Submission.Work.Diff.STE.B3.VarCoef.VarCoefAssembly
import Submission.Work.Diff.STE.B3.VarCoef.rhoLipschitz
import Submission.Work.Diff.STE.B3.VarCoef.mulOp_isOrd
import Submission.Work.Diff.STE.B3.VarCoef.cutOp_isOrd
import Submission.Work.Diff.STE.B3.VarCoef.pdOp_isOrd
import Submission.Work.Diff.STE.B3.VarCoef.commCutMul_isOrd
import Submission.Work.Diff.STE.B3.VarCoef.commMulPd
import Submission.Work.Diff.STE.B3.SymCalcStep8.L2re_le_sqrt_CSqZ
import Submission.Work.Diff.STE.B3.SymCalcStep7.L2re_add

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

Lead design (2026-10-03), the core flat estimate behind ENormB_pair_J_commutator_v2 (H2731). Everything is on the flat torus with PERIODIC smooth coefficients: there are no charts, transfers or periodisation issues here.

CLAIM: X := M_ψ ∘ S ∘ M_ψ (S = flatCut ρ ε) commutes with P := M_{c'} ∘ D^k ∘ M_c (D = varLap A B, a second-order operator with smooth periodic coefficients) up to order 2k−1, uniformly in ε ∈ (0,1]. The statement is the pairing form ⟨F, [X,P] U⟩. It holds for ALL smooth periodic A, B, c, c', ψ: no ellipticity and no symmetry are needed.

Numerically verified on 3.22 (1D torus, random smooth coefficients):
| k | ε = 0.2 | ε = 0.05 | ε = 0.0125 |
|---|---|---|---|
| 1 | 42.6 | 42.4 | 42.4 |
| 2 | 2.39e3 | 2.50e3 | 2.51e3 |
The ratio is flat for N = 40, 80, 120. The uncommuted X P grows like 1/ε for k = 1.

ROUTE (an "order calculus" on the integer Sobolev scale; CSqZ t exists, B3/SymCalcStep8/CSqZ.lean):
1. Building blocks, each stated as ‖Op g‖_{CSqZ(t − ord)} ≤ C ‖g‖_{CSqZ t} for every integer t, uniformly in ε ≤ 1:
   - M_m for smooth periodic m: ord 0 (mul_CSq_le for t ≥ 0; duality for t < 0);
   - pd a: ord 1 (Fourier multiplier 2πi m_a);
   - S = flatCut: ord 0 (|ρ| ≤ 1, flatCut_CSq_le);
   - the commutator [M_m, S]: ord −1, i.e. a GAIN (flat_multiplier_commutator / flat_multiplier_gain, PROVED for t ≥ 0; use duality and the symmetry of S for t < 0).
   S commutes exactly with pd and with lapC, since both are Fourier multipliers.
2. [X, M_m] = M_ψ [S, M_m] M_ψ has ord −1.
   [X, pd a] = −(M_{∂_aψ} S M_ψ + M_ψ S M_{∂_aψ}) has ord 0.
   Hence [X, D] = −Σ_{ab}([X, A_ab] ∂_a∂_b + A_ab([X,∂_a]∂_b + ∂_a[X,∂_b])) − Σ_a([X,B_a] ∂_a + B_a [X,∂_a]) has ord 1.
3. [X, P] = [X, M_{c'}] D^k M_c + M_{c'} (Σ_{j<k} D^j [X, D] D^{k−1−j}) M_c + M_{c'} D^k [X, M_c]. Every term has ord 2k−1.
4. Pairing: |L2re F G| ≤ √CSqZ(k−1) F · √CSqZ(−(k−1)) G (Parseval + Cauchy–Schwarz; abs_L2re_le_sqrt_CSq exists for the nonnegative case). Apply it with G = [X,P]U and t = k: ord 2k−1 maps CSqZ k to CSqZ (−(k−1)).
   CSqZ k = CSq k and CSqZ (k−1) = CSq (k−1) for these natural indices; prove that equality if it is not already present.
Reuse first: grep B3/SymCalcStep7 and SymCalcStep8 (flat_multiplier_gain, mul_CSq_le, flatCut_CSq_le, CSqZ, abs_L2re_le_sqrt_CSq, L2re_selfadj). Split at most once, into (a) the order calculus for multipliers, pd and [M_m, S] on CSqZ, and (b) the assembly. Run python3 REFS/tools/dupcheck.py . | grep VarCoef before declare_proven.
-/

namespace Work.Diff.STE.B3.VarCoef

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Linearity of the real `L²` pairing in its second argument, for a difference. -/
theorem L2re_sub_snd {F g h : (ι → ℝ) → ℂ} (hF : Continuous F) (hg : Continuous g)
    (hh : Continuous h) :
    Work.Diff.STE.L2re F (g - h) = Work.Diff.STE.L2re F g - Work.Diff.STE.L2re F h := by
  have h1 := Work.Diff.STE.B3.SymCalcStep7.L2re_add_snd hF hg hh.neg
  have h2 : Work.Diff.STE.L2re F (-h) = -Work.Diff.STE.L2re F h := by
    simp only [Work.Diff.STE.L2re]
    rw [show (fun x : ι → ℝ => F x * star ((-h) x)) = fun x => -(F x * star (h x)) by
      funext x
      simp only [Pi.neg_apply, star_neg]
      ring]
    rw [MeasureTheory.integral_neg]
    simp
  rw [sub_eq_add_neg, h1, h2]
  ring

/-- The pointwise identity `[M_ψ, ∂_a] = -M_{∂_aψ}` for smooth inputs, in the shape used to
feed `IsOrd.congr`. -/
theorem commOp_mulOp_pdOp_apply {m : (ι → ℝ) → ℝ} (hm : ContDiff ℝ (⊤ : ℕ∞) m) (a : ι)
    (f : (ι → ℝ) → ℂ) (hf : SmoothPer f) :
    commOp (mulOp m) (pdOp a) f = (-(mulOp (Work.Diff.STE.pdR a m))) f := by
  rw [commMulPd m hm a f hf]
  rfl

/-- The pointwise identity `[M_m, M_{m'}] = 0`. -/
theorem commOp_mulOp_mulOp_apply (m m' : (ι → ℝ) → ℝ) (f : (ι → ℝ) → ℂ) :
    commOp (mulOp m) (mulOp m') f = (0 : Op ι) f := by
  funext x
  simp only [commOp_apply, mulOp, Pi.sub_apply, Pi.zero_apply]
  ring

/-- The pointwise identity `[S_ε, ∂_a] = 0` for smooth inputs. -/
theorem commOp_cutOp_pdOp_apply (ρ : (ι → ℝ) → ℝ) (hρ : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1)
    (ε : ℝ) (a : ι) (f : (ι → ℝ) → ℂ) (hf : SmoothPer f) :
    commOp (cutOp ρ ε) (pdOp a) f = (0 : Op ι) f := by
  have h := Work.Diff.STE.B3.SymCalcStep8.pd_flatCut a ρ hρ ε hf.1 hf.2
  simp only [commOp_apply, cutOp, pdOp, Pi.zero_apply]
  rw [sub_eq_zero]
  exact h.symm

theorem varLapPow_cut_comm_pairing {ι : Type*} [Fintype ι] [DecidableEq ι]
    (k : ℕ) (hk : 1 ≤ k)
    (ρ : (ι → ℝ) → ℝ) (hρ : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1)
    (hρ0 : ∀ y : ι → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (hρs : ContDiff ℝ (⊤ : ℕ∞) ρ) (hρ1 : ρ 0 = 1)
    (A : ι → ι → (ι → ℝ) → ℝ) (B : ι → (ι → ℝ) → ℝ) (c c' ψ : (ι → ℝ) → ℝ)
    (hA : ∀ a b, ContDiff ℝ (⊤ : ℕ∞) (A a b)) (hAp : ∀ a b, Work.Diff.STE.Periodic1 (A a b))
    (hB : ∀ a, ContDiff ℝ (⊤ : ℕ∞) (B a)) (hBp : ∀ a, Work.Diff.STE.Periodic1 (B a))
    (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hcp : Work.Diff.STE.Periodic1 c)
    (hc' : ContDiff ℝ (⊤ : ℕ∞) c') (hc'p : Work.Diff.STE.Periodic1 c')
    (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψp : Work.Diff.STE.Periodic1 ψ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ε : ℝ), 0 < ε → ε ≤ 1 → ∀ F U : (ι → ℝ) → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) F → Work.Diff.STE.Periodic1 F →
      ContDiff ℝ (⊤ : ℕ∞) U → Work.Diff.STE.Periodic1 U →
      |Work.Diff.STE.L2re F (fun x => ((ψ x : ℝ) : ℂ) *
            Work.Diff.STE.B3.SymCalc.flatCut ρ ε (fun y => ((ψ y : ℝ) : ℂ) * (((c' y : ℝ) : ℂ) *
              Work.Diff.STE.B3.VarCoef.varLapPow k A B (fun z => ((c z : ℝ) : ℂ) * U z) y)) x)
        - Work.Diff.STE.L2re F (fun x => ((c' x : ℝ) : ℂ) *
            Work.Diff.STE.B3.VarCoef.varLapPow k A B (fun z => ((c z : ℝ) : ℂ) *
              (((ψ z : ℝ) : ℂ) * Work.Diff.STE.B3.SymCalc.flatCut ρ ε
                (fun y => ((ψ y : ℝ) : ℂ) * U y) z)) x)|
        ≤ C * Real.sqrt (Work.Diff.STE.CSq (k - 1) (Work.Diff.STE.fourierCoeff F))
            * Real.sqrt (Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff U)) := by
  classical
  -- the Lipschitz constant of `ρ`
  obtain ⟨L, hL0, hρlip⟩ := rhoLipschitz ρ hρs hρ0
  -- the ε-free order certificates of the individual multipliers
  obtain ⟨Cc, hCc⟩ := mulOp_isOrd c hc hcp
  obtain ⟨Cc', hCc'⟩ := mulOp_isOrd c' hc' hc'p
  obtain ⟨Cψ, hCψ⟩ := mulOp_isOrd ψ hψ hψp
  choose CA hCA using fun (a : ι) (b : ι) => mulOp_isOrd (A a b) (hA a b) (hAp a b)
  choose CB hCB using fun (a : ι) => mulOp_isOrd (B a) (hB a) (hBp a)
  choose Cp hCp using fun (i : ι) => pdOp_isOrd i
  -- the ε-uniform gain constants for `[S_ε, M_m]`
  choose CgA hCgA using fun (a : ι) (b : ι) =>
    commCutMul_isOrd ρ (A a b) (hA a b) (hAp a b) L hL0 hρlip hρ hρ0 hρ1
  choose CgB hCgB using fun (a : ι) =>
    commCutMul_isOrd ρ (B a) (hB a) (hBp a) L hL0 hρlip hρ hρ0 hρ1
  obtain ⟨Cgc, hCgc⟩ := commCutMul_isOrd ρ c hc hcp L hL0 hρlip hρ hρ0 hρ1
  obtain ⟨Cgc', hCgc'⟩ := commCutMul_isOrd ρ c' hc' hc'p L hL0 hρlip hρ hρ0 hρ1
  obtain ⟨Cgψ, hCgψ⟩ := commCutMul_isOrd ρ ψ hψ hψp L hL0 hρlip hρ hρ0 hρ1
  -- `[M_ψ, ∂_i] = -M_{∂_iψ}`: the ε-free constant of the commutator
  choose Cpgψ hCpgψ using fun (i : ι) =>
    mulOp_isOrd (Work.Diff.STE.pdR i ψ) (pdR_contDiff hψ i) (pdR_periodic hψp i)
  -- ### the `varLap` certificate for the cutoff family
  have hS0 : ∀ ε : ℝ, IsOrd 0 (fun _ => 1) (cutOp ρ ε) := fun ε => cutOp_isOrd ρ hρ ε
  have hSl : ∀ ε : ℝ, LinSP (cutOp ρ ε) := fun ε => (cutOp_isOrd ρ hρ ε).lin
  have hSp : ∀ ε : ℝ, Preserves (cutOp ρ ε) := fun ε => (cutOp_isOrd ρ hρ ε).pres
  have hVLcut : ∃ CD CSD : ℤ → ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      IsCommOrd (cutOp ρ ε) 2 CD CSD (varLapOp A B) :=
    ⟨_, _, fun ε hε hε1 => varLap_isCommOrd_exp (cutOp ρ ε) (hSl ε) (hSp ε) A B
      CA (fun a b => CgA a b) CB (fun a => CgB a) Cp (fun _ => fun _ => 0)
      (fun a b => hCA a b) (fun a b => (hCgA a b).2 ε hε hε1) (fun a => hCB a)
      (fun a => (hCgB a).2 ε hε hε1) (fun i => hCp i)
      (fun i => IsOrd.congr (T := (0 : Op ι)) (IsOrd.zero' 0)
        (fun f hf => (commOp_cutOp_pdOp_apply ρ hρ ε i f hf).symm))⟩
  obtain ⟨CD, CSD, hVLcut⟩ := hVLcut
  have hDord : IsOrd 2 CD (varLapOp A B) := (hVLcut 1 (by norm_num) le_rfl).ord
  have hSD : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → IsOrd 1 CSD (commOp (cutOp ρ ε) (varLapOp A B)) :=
    fun ε hε hε1 => (hVLcut ε hε hε1).comm
  -- ### the `varLap` certificate for `M_ψ`
  have hVLM : ∃ CM CMl : ℤ → ℝ, IsCommOrd (mulOp ψ) 2 CM CMl (varLapOp A B) :=
    ⟨_, _, varLap_isCommOrd_exp (mulOp ψ) hCψ.lin hCψ.pres A B
      CA (fun _ _ => fun _ => 0) CB (fun _ => fun _ => 0) Cp Cpgψ
      (fun a b => hCA a b)
      (fun a b => IsOrd.congr (T := (0 : Op ι)) (IsOrd.zero' (-1))
        (fun f _ => (commOp_mulOp_mulOp_apply ψ (A a b) f).symm))
      (fun a => hCB a)
      (fun a => IsOrd.congr (T := (0 : Op ι)) (IsOrd.zero' (-1))
        (fun f _ => (commOp_mulOp_mulOp_apply ψ (B a) f).symm))
      (fun i => hCp i)
      (fun i => IsOrd.congr (T := -(mulOp (Work.Diff.STE.pdR i ψ))) (IsOrd.neg (hCpgψ i))
        (fun f hf => (commOp_mulOp_pdOp_apply hψ i f hf).symm))⟩
  obtain ⟨CM, CMl, hVLM⟩ := hVLM
  -- ### powers of `D` and of the iterated commutators
  have hiter : ∀ j : ℕ, IsOrd (2 * (j : ℤ)) (iterConst CD j) (((varLapOp A B)^[j])) :=
    iterConst_isOrd hDord
  have hpow : ∀ j : ℕ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → IsOrd (2 * (j : ℤ) - 1)
      (commPowConst CSD CD j) (commOp (cutOp ρ ε) (((varLapOp A B)^[j]))) :=
    commPow_unif_fam (S := fun ε => cutOp ρ ε) hDord hSl hSp hSD
  have hpowM : ∀ j : ℕ, IsOrd (2 * (j : ℤ) - 1) (commPowConst CMl CM j)
      (commOp (mulOp ψ) (((varLapOp A B)^[j]))) :=
    fun j => commPow_unif_fam (S := fun _ => mulOp ψ) hVLM.ord (fun _ => hCψ.lin)
      (fun _ => hCψ.pres) (fun _ hε hε1 => hVLM.comm) j 1 (by norm_num) le_rfl
  let CDk : ℤ → ℝ := iterConst CD k
  let CSDk : ℤ → ℝ := commPowConst CSD CD k
  let CMDk : ℤ → ℝ := commPowConst CMl CM k
  have hDk : IsOrd (2 * (k : ℤ)) CDk (((varLapOp A B)^[k])) := hiter k
  have hSDk : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → IsOrd (2 * (k : ℤ) - 1) CSDk
      (commOp (cutOp ρ ε) (((varLapOp A B)^[k]))) := fun ε hε hε1 => hpow k ε hε hε1
  have hMDk : IsOrd (2 * (k : ℤ) - 1) CMDk (commOp (mulOp ψ) (((varLapOp A B)^[k]))) := hpowM k
  -- the commutators with `P = M_{c'} ∘ D^k ∘ M_c`
  obtain ⟨CSP, hSP⟩ := commOp_POp_cut_unif (S := fun ε => cutOp ρ ε) (D := varLapOp A B) hk
    hCc hCc' hS0 hDk hSDk (fun ε hε hε1 => (hCgc).2 ε hε hε1)
    (fun ε hε hε1 => (hCgc').2 ε hε hε1)
  have hPex : ∃ CP : ℤ → ℝ, IsOrd (2 * (k : ℤ)) CP (POp c c' (varLapOp A B) k) :=
    ⟨_, IsOrd.mono_d (d := 2 * (k : ℤ)) (d' := 0 + 2 * (k : ℤ) + 0)
      (IsOrd.comp (T := compOp (mulOp c') (((varLapOp A B)^[k]))) (U := mulOp c)
        (IsOrd.comp (T := mulOp c') (U := ((varLapOp A B)^[k])) hCc' hDk) hCc) (by omega)⟩
  obtain ⟨CP, hP⟩ := hPex
  obtain ⟨CMP, hMP⟩ := commOp_POp_mul_const (D := varLapOp A B) hk hCc hCc' hCψ hDk hMDk
    (IsOrd.congr (T := (0 : Op ι)) (IsOrd.zero' (-1))
      (fun f _ => (commOp_mulOp_mulOp_apply ψ c f).symm))
    (IsOrd.congr (T := (0 : Op ι)) (IsOrd.zero' (-1))
      (fun f _ => (commOp_mulOp_mulOp_apply ψ c' f).symm))
  obtain ⟨CXP, hXP⟩ := commOp_XOp_POp_unif (S := fun ε => cutOp ρ ε) (D := varLapOp A B) hk
    hCψ hS0 (dP := 2 * (k : ℤ)) hP hSP hMP
  -- ### the pairing estimate
  refine ⟨Real.sqrt (CXP k), Real.sqrt_nonneg _, fun ε hε hε1 F U hF hFp hU hUp => ?_⟩
  have hFsp : SmoothPer F := ⟨hF, hFp⟩
  have hUsp : SmoothPer U := ⟨hU, hUp⟩
  have hT := hXP ε hε hε1
  set W : (ι → ℝ) → ℂ := (commOp (XOp ψ (cutOp ρ ε)) (POp c c' (varLapOp A B) k)) U with hWdef
  have hWsp : SmoothPer W := hT.pres U hUsp
  -- the operator bound at `t = k`
  have hbnd : Work.Diff.STE.B3.SymCalcStep8.CSqZ ((k : ℤ) - (2 * (k : ℤ) - 1))
      (Work.Diff.STE.fourierCoeff W)
      ≤ CXP k * Work.Diff.STE.B3.SymCalcStep8.CSqZ (k : ℤ) (Work.Diff.STE.fourierCoeff U) :=
    hT.bound k U hUsp
  have hbnd' : Work.Diff.STE.B3.SymCalcStep8.CSqZ (-((k : ℤ) - 1))
      (Work.Diff.STE.fourierCoeff W)
      ≤ CXP k * Work.Diff.STE.B3.SymCalcStep8.CSqZ (k : ℤ) (Work.Diff.STE.fourierCoeff U) := by
    rw [show (k : ℤ) - (2 * (k : ℤ) - 1) = -((k : ℤ) - 1) from by ring] at hbnd
    exact hbnd
  -- weighted Cauchy–Schwarz
  have hcs := Work.Diff.STE.B3.SymCalcStep8.L2re_le_sqrt_CSqZ ((k : ℤ) - 1) F W hF hFp
    hWsp.1 hWsp.2
  have hFc : Work.Diff.STE.B3.SymCalcStep8.CSqZ ((k : ℤ) - 1) (Work.Diff.STE.fourierCoeff F)
      = Work.Diff.STE.CSq (k - 1) (Work.Diff.STE.fourierCoeff F) := by
    rw [← Work.Diff.STE.B3.SymCalcStep8.CSqZ_natCast (k - 1) (Work.Diff.STE.fourierCoeff F)]
    congr 1
    omega
  have hUc : Work.Diff.STE.B3.SymCalcStep8.CSqZ (k : ℤ) (Work.Diff.STE.fourierCoeff U)
      = Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff U) :=
    Work.Diff.STE.B3.SymCalcStep8.CSqZ_natCast k _
  have hs2 : Real.sqrt (Work.Diff.STE.B3.SymCalcStep8.CSqZ (-((k : ℤ) - 1))
        (Work.Diff.STE.fourierCoeff W))
      ≤ Real.sqrt (CXP k) * Real.sqrt (Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff U)) := by
    calc Real.sqrt (Work.Diff.STE.B3.SymCalcStep8.CSqZ (-((k : ℤ) - 1))
          (Work.Diff.STE.fourierCoeff W))
        ≤ Real.sqrt (CXP k * Work.Diff.STE.B3.SymCalcStep8.CSqZ (k : ℤ)
            (Work.Diff.STE.fourierCoeff U)) := Real.sqrt_le_sqrt hbnd'
      _ = Real.sqrt (CXP k) * Real.sqrt (Work.Diff.STE.B3.SymCalcStep8.CSqZ (k : ℤ)
            (Work.Diff.STE.fourierCoeff U)) := Real.sqrt_mul (hT.nonneg k) _
      _ = Real.sqrt (CXP k) * Real.sqrt (Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff U)) := by
          rw [hUc]
  have hgoal1 : |Work.Diff.STE.L2re F W| ≤ Real.sqrt (CXP k)
      * Real.sqrt (Work.Diff.STE.CSq (k - 1) (Work.Diff.STE.fourierCoeff F))
      * Real.sqrt (Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff U)) := by
    calc |Work.Diff.STE.L2re F W|
        ≤ Real.sqrt (Work.Diff.STE.B3.SymCalcStep8.CSqZ ((k : ℤ) - 1)
              (Work.Diff.STE.fourierCoeff F))
            * Real.sqrt (Work.Diff.STE.B3.SymCalcStep8.CSqZ (-((k : ℤ) - 1))
              (Work.Diff.STE.fourierCoeff W)) := hcs
      _ = Real.sqrt (Work.Diff.STE.CSq (k - 1) (Work.Diff.STE.fourierCoeff F))
            * Real.sqrt (Work.Diff.STE.B3.SymCalcStep8.CSqZ (-((k : ℤ) - 1))
              (Work.Diff.STE.fourierCoeff W)) := by rw [hFc]
      _ ≤ Real.sqrt (Work.Diff.STE.CSq (k - 1) (Work.Diff.STE.fourierCoeff F))
            * (Real.sqrt (CXP k) * Real.sqrt (Work.Diff.STE.CSq k
              (Work.Diff.STE.fourierCoeff U))) :=
          mul_le_mul_of_nonneg_left hs2 (Real.sqrt_nonneg _)
      _ = Real.sqrt (CXP k) * Real.sqrt (Work.Diff.STE.CSq (k - 1)
              (Work.Diff.STE.fourierCoeff F))
            * Real.sqrt (Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff U)) := by ring
  -- the target's difference is the pairing with the commutator
  have hXp : Preserves (XOp ψ (cutOp ρ ε)) :=
    Preserves.comp (T := compOp (mulOp ψ) (cutOp ρ ε)) (U := mulOp ψ)
      (Preserves.comp (T := mulOp ψ) (U := cutOp ρ ε) hCψ.pres (hSp ε)) hCψ.pres
  have hAsm : SmoothPer (XOp ψ (cutOp ρ ε) (POp c c' (varLapOp A B) k U)) :=
    hXp _ (hP.pres U hUsp)
  have hBsm : SmoothPer (POp c c' (varLapOp A B) k (XOp ψ (cutOp ρ ε) U)) :=
    hP.pres _ (hXp U hUsp)
  have hsub : Work.Diff.STE.L2re F (XOp ψ (cutOp ρ ε) (POp c c' (varLapOp A B) k U))
        - Work.Diff.STE.L2re F (POp c c' (varLapOp A B) k (XOp ψ (cutOp ρ ε) U))
      = Work.Diff.STE.L2re F W := by
    rw [hWdef]
    simp only [commOp_apply]
    rw [L2re_sub_snd hF.continuous hAsm.1.continuous hBsm.1.continuous]
  show |Work.Diff.STE.L2re F (XOp ψ (cutOp ρ ε) (POp c c' (varLapOp A B) k U))
      - Work.Diff.STE.L2re F (POp c c' (varLapOp A B) k (XOp ψ (cutOp ρ ε) U))|
      ≤ Real.sqrt (CXP k) * Real.sqrt (Work.Diff.STE.CSq (k - 1) (Work.Diff.STE.fourierCoeff F))
          * Real.sqrt (Work.Diff.STE.CSq k (Work.Diff.STE.fourierCoeff U))
  rw [hsub]
  exact hgoal1

end Work.Diff.STE.B3.VarCoef
