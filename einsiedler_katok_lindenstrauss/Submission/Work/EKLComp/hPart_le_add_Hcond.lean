import Mathlib
import Submission.Work.EKLComp.prop92defs
import Submission.Work.EKLComp.prop92win.hPart_winPart

/-!
# `hPart ν a Q ≤ hPart ν a P + H_ν(Q | past Q ∨ orbit P)`

EKL Prop. 9.2 uses the relative-entropy identity
`h_μ(T, P ∨ Q) = h_μ(T, P) + h_μ(T, Q | ⋁_{i∈ℤ} T^i P)`
together with the monotonicity of `hPart` under refinement to compare the entropies of two
partitions.  The quantity `h_μ(T, Q | 𝓐)` of the paper is, by definition,
`H_μ(Q | ⋁_{n≥1} T^{-n} Q ∨ 𝓐)`, so that the relevant σ-algebra is

`negOrbitSigma t Q ⊔ orbitSigma t P = ⋁_{n≥1} T^{-n}Q ⊔ ⋁_{i∈ℤ} T^i P`.

The proof below follows the chain-rule step of `Work.EKLComp.prop92`.  The only extra ingredient
is that the *family* of σ-algebras `Cwin t P Q m` (whose `sup` is `orbitSigma t P ⊔ pastSig t Q`)
exhausts the target σ-algebra in the limit: each `Cwin t P Q m` already contains the two-sided
window of `P` of width `m`, so `⨆_m Cwin t P Q m ≥ orbitSigma t P ⊔ pastSig t Q`.  Passing to
the `m → ∞` limit (`tendsto_Hcond_iSup`) turns the finitary chain rule into the claimed identity.
-/

open MeasureTheory Filter Topology
open scoped ENNReal BigOperators
open LeanEval.Dynamics.EinsiedlerKatokLindenstrauss

noncomputable section

set_option maxHeartbeats 4000000

namespace Work.EKLComp

open Work.EKLContract

/-- `shiftZ t 1` is the map `x ↦ aDiag t • x`. -/
theorem aDiag_smul_eq_shiftZ_one (t : Fin 3 → ℝ) :
    (fun x : X3 => aDiag t • x) = shiftZ t 1 := by
  funext x
  simp [shiftZ, aZ_one]

/-- The integer powers `shiftZ t n` are the iterates of `shiftZ t 1`. -/
theorem shiftZ_iterate_eq (t : Fin 3 → ℝ) (n : ℕ) :
    (shiftZ t 1)^[n] = shiftZ t (n : ℤ) := by
  induction n with
  | zero => rw [Function.iterate_zero, Nat.cast_zero, shiftZ_zero]
  | succ n ih =>
      rw [Function.iterate_succ, ih, ← shiftZ_add]
      congr 1

/-- `pastSig t Q` (the past σ-algebra `⋁_{n≥1} T^{-n}Q` of `Q` for `T = shiftZ t 1`) is literally
`negOrbitSigma t Q`. -/
theorem pastSig_eq_negOrbitSigma (t : Fin 3 → ℝ) (Q : FinPart X3) :
    pastSig t Q = negOrbitSigma t Q := by
  have heq : ∀ n : ℕ, (shiftZ t 1)^[n + 1] = fun x : X3 => aZ t ((n : ℤ) + 1) • x := by
    intro n
    rw [shiftZ_iterate_eq t (n + 1),
      show ((n + 1 : ℕ) : ℤ) = (n : ℤ) + 1 from by push_cast; ring]
    rfl
  unfold pastSig negOrbitSigma
  refine le_antisymm (iSup_le fun n => ?_) (iSup_le fun n => ?_)
  · rw [heq n]
    exact le_iSup (fun n : ℕ =>
      MeasurableSpace.comap (fun x : X3 => aZ t ((n : ℤ) + 1) • x) (partSigma Q)) n
  · rw [← heq n]
    exact le_iSup (fun n : ℕ => MeasurableSpace.comap ((shiftZ t 1)^[n + 1]) (partSigma Q)) n

theorem hPart_le_add_Hcond {t : Fin 3 → ℝ} (ν : MeasureTheory.Measure Work.EKLContract.X3) [MeasureTheory.IsProbabilityMeasure ν] (hmp : MeasureTheory.MeasurePreserving (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) ν ν) (P Q : Work.EKLContract.FinPart Work.EKLContract.X3) : Work.EKLContract.hPart ν (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) Q ≤ Work.EKLContract.hPart ν (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t • x) P + @Work.EKLContract.Hcond Work.EKLContract.X3 Work.EKLContract.instMeasurableSpaceX3 ν Q (Work.EKLComp.negOrbitSigma t Q ⊔ Work.EKLComp.orbitSigma t P) := by
  have hT : (fun x : X3 => aDiag t • x) = shiftZ t 1 := aDiag_smul_eq_shiftZ_one t
  rw [hT] at hmp ⊢
  -- The finitary chain rule: for every window width `m`,
  -- `hPart ν T Q ≤ hPart ν T P + H_ν(Q | Cwin t P Q m)`.
  have hchain : ∀ m : ℕ, hPart ν (shiftZ t 1) Q
      ≤ hPart ν (shiftZ t 1) P + Hcond ν Q (Cwin t P Q m) := by
    intro m
    have hR : hPart ν (shiftZ t 1) (joinPart__USCBasic (winPart t P m) Q)
        = Hcond ν (joinPart__USCBasic (winPart t P m) Q) (pastSig t (joinPart__USCBasic (winPart t P m) Q)) :=
      hPart_eq_Hcond_pastSig (ν := ν) t hmp _
    have hpart_le : partSigma (winPart t P m) ≤ partSigma (joinPart__USCBasic (winPart t P m) Q) := by
      rw [partSigma_joinPart]; exact le_sup_left
    have hpast_le : pastSig t (winPart t P m) ≤ pastSig t (joinPart__USCBasic (winPart t P m) Q) := by
      unfold pastSig
      refine iSup_le fun n => ?_
      exact le_trans (MeasurableSpace.comap_mono hpart_le)
        (le_iSup (fun n' : ℕ => MeasurableSpace.comap ((shiftZ t 1)^[n' + 1])
          (partSigma (joinPart__USCBasic (winPart t P m) Q))) n)
    calc hPart ν (shiftZ t 1) Q
        ≤ hPart ν (shiftZ t 1) (joinPart__USCBasic (winPart t P m) Q) :=
          hPart_le_of_refines ν (measurable_shiftZ t 1) (Refines_joinPart_right _ _)
      _ = Hcond ν (joinPart__USCBasic (winPart t P m) Q) (pastSig t (joinPart__USCBasic (winPart t P m) Q)) := hR
      _ = Hcond ν (winPart t P m) (pastSig t (joinPart__USCBasic (winPart t P m) Q))
            + Hcond ν Q (pastSig t (joinPart__USCBasic (winPart t P m) Q) ⊔ partSigma (winPart t P m)) :=
          Hcond_joinPart ν (winPart t P m) Q _
      _ ≤ Hcond ν (winPart t P m) (pastSig t (winPart t P m))
            + Hcond ν Q (Cwin t P Q m) :=
          add_le_add (Hpart.Hcond_mono_alg ν (winPart t P m) hpast_le) le_rfl
      _ = hPart ν (shiftZ t 1) (winPart t P m) + Hcond ν Q (Cwin t P Q m) := by
          rw [← hPart_eq_Hcond_pastSig (ν := ν) t hmp (winPart t P m)]
      _ = hPart ν (shiftZ t 1) P + Hcond ν Q (Cwin t P Q m) := by
          rw [prop92win.hPart_winPart t hmp P m]
  -- The σ-algebras `Cwin t P Q m` exhaust `negOrbitSigma t Q ⊔ orbitSigma t P`.
  have hMle : negOrbitSigma t Q ⊔ orbitSigma t P ≤ ⨆ m, Cwin t P Q m := by
    rw [← pastSig_eq_negOrbitSigma t Q, sup_comm]
    exact le_iSup_Cwin t P Q
  have htend : Tendsto (fun m => Hcond ν Q (Cwin t P Q m)) atTop
      (nhds (Hcond ν Q (⨆ m, Cwin t P Q m))) :=
    Hpart.tendsto_Hcond_iSup ν Q _ (Cwin_mono t P Q) (Cwin_le t P Q)
  have hle : Hcond ν Q (⨆ m, Cwin t P Q m)
      ≤ Hcond ν Q (negOrbitSigma t Q ⊔ orbitSigma t P) :=
    Hpart.Hcond_mono_alg ν Q hMle
  refine le_of_forall_pos_le_add fun ε hε => ?_
  have hlt : Hcond ν Q (⨆ m, Cwin t P Q m)
      < Hcond ν Q (negOrbitSigma t Q ⊔ orbitSigma t P) + ε := by linarith
  obtain ⟨N, hN⟩ := eventually_atTop.1 (htend.eventually (isOpen_Iio.mem_nhds hlt))
  have hfin : Hcond ν Q (Cwin t P Q N)
      < Hcond ν Q (negOrbitSigma t Q ⊔ orbitSigma t P) + ε := by
    linarith [hN N le_rfl, hle, hε]
  have hgoal : hPart ν (shiftZ t 1) P + Hcond ν Q (Cwin t P Q N)
      ≤ (hPart ν (shiftZ t 1) P + Hcond ν Q (negOrbitSigma t Q ⊔ orbitSigma t P)) + ε := by
    linarith [hfin]
  exact le_trans (hchain N) hgoal

end Work.EKLComp
