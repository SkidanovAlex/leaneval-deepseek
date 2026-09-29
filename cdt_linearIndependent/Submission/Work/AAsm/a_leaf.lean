import Mathlib
import Submission.CDTPlan.InterfacesA2
import Submission.Work.AAsm.phiAfam_admissible
import Submission.Work.AAsm.phiAfam_deriv
import Submission.Work.AAsm.a_log_bounds
import Submission.Work.AAsm.exists_int_relation_a

/-! Guidance from the project lead (the requester):

# Area AAsm — assembly of Theorem A (`ALeaf = Submission.CDT.theoremA_leaf`)
Suppose L(2,χ₋₃) = a₀ + b₀ζ(2) (a₀, b₀ ∈ ℚ) — read the exact form of `theoremA_leaf` (TheoremA_leaf.lean)
and relate `ZMod.LFunction chi3 2`, `riemannZeta 2` to `Submission.CDT.L2chi3Real`, `zeta2Real` (the prior
run has these bridges in L2chi3Real/L2chi3Corollary — grep). Clear denominators: a + b·L/2 + c·ζ/4 = 0
with integers, b ≠ 0 (coefficient of L). Apply hH with m = 14, r = 2, l = 2, b = bA, e = eA,
f = fourteen a b c, φ = phiAfam (maps φ_A(z/10⁴), φ_A(283z/500), φ_A), γ = gammaA = (0, 71/125, 277/100, 14),
ξ = 2:
- ColumnShape bA (fin_cases), hD, h14, hC;
- AdmissibleMap for the three maps (PsiAFacts + HauptFacts; zero-free on the circle: φ_A(z) = 0 ⇔ z = 0);
- PullbackMero: hPB for φ_A, then hSc with ρ = 1/10⁴ and 283/500;
- conformality and StrictMono: |φ_k'(0)| = ρ_k·256·|ψ_A'(0)| with ρ = (1e-4, 0.566, 1);
- τ = 16603/3920 (hT) < L := log(256·|ψ_A'(0)|) = 5.08539… (|ψ_A'(0)| exact from hN).
Numbers: 14(L − τ) = 11.899…; RHS = rearrInt ≤ 11.2 (hN) + (1/14)[(71/125)²·log 5660 + (277/100)²·log(500/283)]
= 11.2 + 0.5111 = 11.711 < 11.899: contradiction (margin 0.19; prove log bounds with Mathlib exp/log
estimates: log 5660 < 8.642, log(500/283) < 0.5692, L > 5.085).
Contracts: `Submission/CDTPlan/InterfacesA2.lean` (Theorem A template), `InterfacesA.lean` (ψ_A, φ_A,
ANumerics, Zagier integrality), `InterfacesC.lean` (intY, tq, dY), `Interfaces.lean`.
The Theorem-C side has already solved the analogous pieces — REUSE, do not rebuild:
`Submission/Work/CPhi/` (lift of φ_C), `Submission/Work/CPull/` (germs.lean: `germ_of_even`,
`pullbackMero_of_germ`, `germ_intY`, `germ_tq`, pullbackMero_B2/B3/B4, deriv_phiC_zeros_finite),
`Submission/Work/CLift/` (continuation of P along Φ with OdeContinuation),
`Submission/Work/CDcl/` (symmetrised-powers route to the d/dy-closure), `Submission/Work/CDen/`.
Axiom-clean A-side facts: `Submission.Work.Purge.a_side_clean` bundles HA_ode, HB_ode, HC_ode,
GA_odeLHS_eq_zero, Cintegral/Aintegral identities, overconvergesB/C (use it instead of the
native_decide-tainted originals); `Work.ZagBI` re-proved HA_ode cleanly too. Never depend on
`native_decide` (check #print axioms).
-/

/-! ## Proof

Assembly of Theorem A from the ten contract hypotheses, mirroring
`Work.CAsm.c_pos` (the Theorem-C analogue).

* `L(2,χ₋₃) = a + b·ζ(2)` (`a b : ℚ`) is transported to the real form
  `L2chi3Real = a + b·zeta2Real` (`LFunction_chi3_two_eq_L2chi3Real`, `zeta2Real_eq_pi`,
  `riemannZeta_two`) and cleared to the integer relation `ARel A B C` with `B ≠ 0`
  (`Work.AAsm.exists_int_relation_a`).
* The ten hypotheses `h14 hD hC hPB` supply `PolyIndependent`, `HasDenomType`, `DClosed` and the
  meromorphic pullbacks along `φ_A`; `hSc : PullbackScale` transports the pullbacks to
  `φ_A(z/10⁴)` and `φ_A(283z/500)` (`phiAfam 0`, `phiAfam 1`).
* `Work.AAsm.phiAfam_admissible` (from `hP`, `hM`) gives the three `AdmissibleMap`s;
  `Work.AAsm.phiAfam_deriv` gives `φ_A'(0) = -256·ψ_A'(0)`, hence — with `‖ψ_A'(0)‖` from
  `hN` — the three conformal sizes `D/10⁴`, `(283/500)D`, `D` with `D = 256·‖ψ_A'(0)‖`
  (positive, strictly increasing, so `StrictMono`).
* `HolonomyBoundL2` at `m = 14`, `l = 2`, `b = bA`, `e = eA`, `φ = phiAfam`,
  `γ = gammaA`, `ξ = 2` yields the inequality
  `14(log D − τ) ≤ rearrInt + (1/14)[(71/125)² log 5660 + (277/100)² log(500/283)]`
  with `τ = 16603/3920` (`hT`).
* The numerics finish it: `rearrInt ≤ 112/10` (`hN`), the two correction logs
  (`Work.AAsm.a_log_bounds`) and `log D > 127/25` give
  `RHS < 410102449/35000000 < 16553/1400 < 14(log D − τ)` — a contradiction.
-/

namespace Work.AAsm

open Complex Metric Submission.CDTPlan

set_option maxHeartbeats 800000


theorem a_leaf (hH : HolonomyBoundL2) (h14 : Fourteen) (hD : ADenoms) (hC : ADClosed)
    (hPB : APullbacks) (hSc : PullbackScale) (hN : ANumerics) (hT : TauValues)
    (hP : PsiAFacts) (hM : HauptFacts) : ALeaf := by
  intro a b hbad
  -- ## bridge: `L(2,χ₋₃) = a + b·ζ(2)` in ℝ
  have hzeta : ((Submission.CDT.zeta2Real : ℝ) : ℂ) = riemannZeta 2 := by
    rw [Submission.CDT.zeta2Real_eq_pi, riemannZeta_two]; push_cast; ring
  have hbadR : Submission.CDT.L2chi3Real = (a : ℝ) + (b : ℝ) * Submission.CDT.zeta2Real := by
    apply Complex.ofReal_inj.mp
    push_cast
    rw [← Submission.CDT.LFunction_chi3_two_eq_L2chi3Real, hzeta]
    exact hbad
  -- ## clear denominators
  obtain ⟨A, B, C, hBne, hrel⟩ := exists_int_relation_a a b hbadR
  -- ## the ten contract hypotheses
  have hPoly : PolyIndependent (fourteen A B C) := h14 A B C hrel hBne
  have hDen : ∀ i, HasDenomType (eA i) (bA i) (fourteen A B C i) := fun i => hD A B C i
  have hDcl : DClosed (fourteen A B C) := hC A B C
  have hAdm : ∀ k : Fin 3, AdmissibleMap (phiAfam k) := phiAfam_admissible hP hM
  obtain ⟨-, hderiv0, hderiv1, hderiv2⟩ := phiAfam_deriv hP hM
  -- ## conformal sizes
  set q : ℝ := (2383521894760738000000000 : ℝ) / 3774888615849058882987209 with hqdef
  set D : ℝ := 256 * q with hDdef
  have hNq : ‖deriv psiA 0‖ = q := hN.1
  have hD0 : ‖deriv (phiAfam 0) 0‖ = (1 / 10000 : ℝ) * D := by rw [hderiv0, hNq, hDdef]
  have hD1 : ‖deriv (phiAfam 1) 0‖ = (283 / 500 : ℝ) * D := by rw [hderiv1, hNq, hDdef]
  have hD2 : ‖deriv (phiAfam 2) 0‖ = D := by rw [hderiv2, hNq, hDdef]
  have hqpos : 0 < q := by rw [hqdef]; norm_num
  have hDpos : 0 < D := by rw [hDdef]; nlinarith [hqpos]
  have hpos0 : 0 < ‖deriv (phiAfam 0) 0‖ := by rw [hD0]; nlinarith [hDpos]
  have hpos1 : 0 < ‖deriv (phiAfam 1) 0‖ := by rw [hD1]; nlinarith [hDpos]
  have hpos2 : 0 < ‖deriv (phiAfam 2) 0‖ := by rw [hD2]; exact hDpos
  have hpos : ∀ k : Fin 3, 0 < ‖deriv (phiAfam k) 0‖ := by
    intro k; fin_cases k
    · exact hpos0
    · exact hpos1
    · exact hpos2
  have hmono : StrictMono (fun k : Fin 3 => ‖deriv (phiAfam k) 0‖) := by
    have hval : (fun k : Fin 3 => ‖deriv (phiAfam k) 0‖)
        = ![(1 / 10000 : ℝ) * D, (283 / 500 : ℝ) * D, D] := by
      funext k; fin_cases k <;> simp [hD0, hD1, hD2]
    rw [hval]
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all <;> nlinarith
  -- ## the partition γ
  have hgam0 : gammaA 0 = 0 := rfl
  have hgamlast : gammaA (Fin.last (2 + 1)) = ((14 : ℕ) : ℝ) := rfl
  have hgammono : StrictMono gammaA := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [gammaA] <;> norm_num
  -- ## the denominator shape
  have hCol : ColumnShape bA := by
    intro j; fin_cases j
    · exact ⟨1, 2, by intro i; fin_cases i <;> simp [bA]⟩
    · exact ⟨3, 2, by intro i; fin_cases i <;> simp [bA]⟩
  -- ## pullbacks along the three maps
  have hφ0 : (fun z : ℂ => phiA ((1 / 10000 : ℝ) * z)) = phiAfam 0 := by
    funext z; show phiA ((1 / 10000 : ℝ) * z) = phiA (z / 10000); congr 1; push_cast; ring
  have hφ1 : (fun z : ℂ => phiA ((283 / 500 : ℝ) * z)) = phiAfam 1 := by
    funext z; show phiA ((283 / 500 : ℝ) * z) = phiA (283 * z / 500); congr 1; push_cast; ring
  have hφ2 : phiA = phiAfam 2 := rfl
  have hpull0 : ∀ i, PullbackMero (fourteen A B C i) (phiAfam 0) := fun i => by
    rw [← hφ0]; exact hSc _ phiA (1 / 10000) (by norm_num) (by norm_num) (hPB A B C hrel i)
  have hpull1 : ∀ i, PullbackMero (fourteen A B C i) (phiAfam 1) := fun i => by
    rw [← hφ1]; exact hSc _ phiA (283 / 500) (by norm_num) (by norm_num) (hPB A B C hrel i)
  have hpull2 : ∀ i, PullbackMero (fourteen A B C i) (phiAfam 2) := fun i => by
    rw [← hφ2]; exact hPB A B C hrel i
  have hpull : ∀ i k, PullbackMero (fourteen A B C i) (phiAfam k) := by
    intro i k
    fin_cases k
    · exact hpull0 i
    · exact hpull1 i
    · exact hpull2 i
  -- ## the τ-hypothesis
  have hlogD : Real.log D > 127 / 25 := by
    rw [hDdef, hqdef]; exact a_log_bounds.1
  have htau : tauFlat bA + tauSharpAt eA 2 < Real.log ‖deriv (phiAfam (Fin.last 2)) 0‖ := by
    rw [show (Fin.last 2 : Fin 3) = 2 from rfl, hD2, hT.2]
    linarith [hlogD]
  -- ## apply the holonomy bound
  have hbound := hH 14 2 2 bA eA (fourteen A B C) phiAfam gammaA 2
    (by norm_num) (by norm_num) hCol hDen hPoly hDcl hAdm hpull hpos hmono
    hgam0 hgamlast hgammono (by norm_num) (by norm_num) htau
  -- ## normalise the conclusion
  set R : ℝ := rearrInt (fun k : Fin 3 => (gammaA k.succ - gammaA k.castSucc) / 14) phiAfam with hRdef
  set S : ℝ := (∑ k : Fin 2, (gammaA k.succ.castSucc) ^ 2 *
          Real.log (‖deriv (phiAfam k.succ) 0‖ / ‖deriv (phiAfam k.castSucc) 0‖)) with hSdef
  have hN' : R ≤ 112 / 10 := hN.2.1
  have hmain : (14 : ℝ) * (Real.log D - 16603 / 3920) ≤ R + (1 / 14) * S := by
    rw [show (Fin.last 2 : Fin 3) = 2 from rfl, hD2, hT.2] at hbound
    exact hbound
  -- ## numeric upper bounds
  have hRval : R = rearrInt (fun k : Fin 3 => (gammaA k.succ - gammaA k.castSucc) / 14) phiAfam := hRdef
  have hr0 : ‖deriv (phiAfam 1) 0‖ / ‖deriv (phiAfam 0) 0‖ = 5660 := by
    rw [hD1, hD0, div_eq_iff (by positivity : (1 / 10000 : ℝ) * D ≠ 0)]
    ring_nf
  have hr1 : ‖deriv (phiAfam 2) 0‖ / ‖deriv (phiAfam 1) 0‖ = (500 : ℝ) / 283 := by
    rw [hD2, hD1, div_eq_iff (by positivity : (283 / 500 : ℝ) * D ≠ 0)]
    ring_nf
  have hScast : S = (∑ k : Fin 2, (gammaA k.succ.castSucc) ^ 2 *
        Real.log (‖deriv (phiAfam k.succ) 0‖ / ‖deriv (phiAfam k.castSucc) 0‖)) := hSdef
  have hS : S = (71 / 125 : ℝ) ^ 2 * Real.log 5660
        + (277 / 100 : ℝ) ^ 2 * Real.log ((500 : ℝ) / 283) := by
    rw [hSdef, Fin.sum_univ_two]
    rw [show ((0 : Fin 2).succ.castSucc : Fin 4) = 1 from rfl,
        show ((0 : Fin 2).succ : Fin 3) = 1 from rfl,
        show ((0 : Fin 2).castSucc : Fin 3) = 0 from rfl,
        show ((1 : Fin 2).succ.castSucc : Fin 4) = 2 from rfl,
        show ((1 : Fin 2).succ : Fin 3) = 2 from rfl,
        show ((1 : Fin 2).castSucc : Fin 3) = 1 from rfl,
        hr0, hr1,
        show gammaA 1 = (71 / 125 : ℝ) from rfl,
        show gammaA 2 = (277 / 100 : ℝ) from rfl]
  have hSbound : S ≤ (71 / 125 : ℝ) ^ 2 * (173 / 20) + (277 / 100 : ℝ) ^ 2 * (29 / 50) := by
    rw [hS]
    nlinarith [a_log_bounds.2.1, a_log_bounds.2.2]
  have hRHS : R + (1 / 14) * S < 410102449 / 35000000 := by
    nlinarith [hN', hSbound]
  have hLHS : (14 : ℝ) * (Real.log D - 16603 / 3920) > 16553 / 1400 := by
    nlinarith [hlogD]
  linarith [hmain, hRHS, hLHS]

end Work.AAsm
