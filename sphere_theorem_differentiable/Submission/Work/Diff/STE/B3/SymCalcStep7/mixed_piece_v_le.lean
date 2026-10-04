import Mathlib
import Submission.Work.Diff.STE.B3.SymCalcStep7.mul_CSq_le
import Submission.Work.Diff.STE.B3.SymCalcStep7.flatCut_CSq_le
import Submission.Work.Diff.STE.B3.SymCalcStep7.conjCut_CSq_le
import Submission.Work.Diff.STE.B3.SymCalcStep7.double_comm_conjLapPow_le
import Submission.Work.Diff.STE.B3.SymCalcStep7.conjLapPow_sub
import Submission.Work.Diff.STE.B3.SymCalcStep7.mixed_transport_identity
import Submission.Work.Diff.STE.B3.SymCalcStep7.flat_multiplier_gain
import Submission.Work.Diff.STE.B3.SymCalcStep6.conj_cut_comm_lapPow_le
import Submission.Work.Diff.STE.B3.SymCalcStep6.conjCut_multiplier_gain
import Submission.Work.Diff.STE.B3.SymCalcStep6.conjLapPow_mul_comm_le
import Submission.Work.Diff.STE.B3.SymCalcStep6.lapPow_toolbox
import Submission.Work.Diff.STE.B3.SymCalcStep6.lapPow_algebra
import Submission.Work.Diff.STE.B3.SymCalcStep1.conj_cut_aux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3.SymCalcStep7

/-!
# The `d`-mixed piece `c·[V, M_d](Λ^k g)` of the six-term decomposition of `pairOp`

## The route actually taken (a *variant* of the one sketched in the target's docstring)

The docstring above the target suggests working in the **chart-`1`** variable with the four-term
expansion `[[V,M_d],Λ^k] = [V,Λ^k]M_d + V[M_d,Λ^k] − M_d[V,Λ^k] − [M_d,Λ^k]V`.  That route needs
the additivity of `Λ^k = lapPow k` **and** of `V = conjCut ρ ε T T'` on differences of smooth
`1`-periodic functions (because `Λ^k(Cg)` and `V([M_d,Λ^k]g)` have to be split); only the first of
those is available in the workspace (`lapPow_algebra.2`, and `flatCut`/`conjCut` are only known to
commute with *negation*, `flatCut_neg`/`conjCut_neg`).

The proof below instead transfers the whole estimate into the **chart-`2`** variable, where the
*cutoff* is the flat `S_ε = flatCut ρ ε` and the Laplacian power is `P_k = conjLapPow k T T'`, so
that the two certificates already in the workspace apply *verbatim*:

* `Work.Diff.STE.B3.SymCalcStep7.mixed_transport_identity` (pure rewriting, `T ∘ T' = id`):

  `M_d(V(Λ^k g)) − V(M_d(Λ^k g)) = compMap T' ([M_{d∘T}, S_ε](P_k h))`,  `h = compMap T g`,

  so (with an overall sign, immaterial for `CSq`) the target is
  `CSq s (fourierCoeff (c · compMap T' W))` with `W = [M_β,S_ε](P_k h)`, `β = compMap T d`.
  The multiplier `c` and the two conjugations are handled by `mul_CSq_le` and
  `fourierCoeff_comp_le` at the levels `s` and `s+2k−1`;
* `Work.Diff.STE.B3.SymCalcStep7.mixed_core_le` (below): the core estimate
  `CSq s (fourierCoeff W) ≤ C · CSq (s+2k−1) (fourierCoeff h)`.  Its proof is the identity

  `[M_β,S_ε](P_k h) = [[M_β,S_ε],P_k]h + P_k([M_β,S_ε]h)`

  (the `u − v` form of the additivity of `P_k`, `Work…SymCalcStep7.conjLapPow_sub`, itself from
  `conjLapPow_add`), whose two pieces are bounded by

  – `double_comm_conjLapPow_le` (the four-term double commutator `f·(B1+B2−B3−B4)`, level `s`
    from level `s+2k−1`), and
  – `conjLapPow_CSq_le` (order `2k`) followed by the `ε`-gain `flat_multiplier_gain`
    (the function form of `SymCalcStep1.flat_multiplier_commutator`) at parameter `s+2k−1`.

This needs only the additivity of `conjLapPow` (available as `conjLapPow_add`).  The same route —
with an additional outer multiplier — is the statement of the sibling target
`Work.Diff.STE.B3.SymCalcStep7.mixed_piece_b_le`; `mixed_core_le` here is that statement at outer
multiplier `a = 1`, proved inline so that the present file has no dependency on that file.

The pointwise identity between `W` and the four-atom expression `Z` occurring in
`double_comm_conjLapPow_le` (together with the additivity `P_k(u−v) = P_k u − P_k v`) is proved by
`funext` + `ring`, the atoms being the individual applications of `S_ε`, `P_k` and `M_β`.
-/

/-- **The core certificate of the `d`-mixed piece**, in the chart-`2` variable:

  `CSq s (fourierCoeff ([M_β, S_ε](P_k h))) ≤ C · CSq (s + 2k − 1) (fourierCoeff h)`,

`ε`-uniformly, with `S_ε = flatCut ρ ε` the Friedrichs cutoff and `P_k = conjLapPow k T T'` the
chart-`1` Laplacian power read in the chart-`2` variable.  Route: the identity
`[M_β,S_ε](P_k h) = [[M_β,S_ε],P_k]h + P_k([M_β,S_ε]h)` (the `u − v` form of the additivity of
`P_k`), whose two pieces are bounded by `double_comm_conjLapPow_le` (four-term double commutator,
level `s` from level `s+2k−1`) and by `conjLapPow_CSq_le` (order `2k`) followed by the `ε`-gain
`flat_multiplier_gain` at parameter `s+2k−1`. -/
theorem mixed_core_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : (ι → ℝ) → ℝ) (hρb : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1)
    (hdiam : ∀ y : ι → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (hρ0 : ρ 0 = 1)
    (L : ℝ) (hL : 0 ≤ L) (hρlip : ∀ y z : ι → ℝ, ‖ρ y - ρ z‖ ≤ L * ‖y - z‖)
    (T T' : (ι → ℝ) → (ι → ℝ)) (hT : ContDiff ℝ (⊤ : ℕ∞) T) (hT' : ContDiff ℝ (⊤ : ℕ∞) T')
    (hTinv1 : ∀ x : ι → ℝ, T' (T x) = x) (hTinv2 : ∀ y : ι → ℝ, T (T' y) = y)
    (hTper : ∀ (i : ι) (x : ι → ℝ), T (x + Pi.single i 1) = T x + Pi.single i 1)
    (β : (ι → ℝ) → ℂ) (hβ : ContDiff ℝ (⊤ : ℕ∞) β) (hβp : Work.Diff.STE.Periodic1 β)
    (k : ℕ) (hk : 1 ≤ k) (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ε : ℝ), 0 < ε → ε ≤ 1 → ∀ h : (ι → ℝ) → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) h → Work.Diff.STE.Periodic1 h →
      Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (fun x => β x *
            Work.Diff.STE.B3.SymCalc.flatCut ρ ε
              (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' h) x
          - Work.Diff.STE.B3.SymCalc.flatCut ρ ε
              (fun y => β y * Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' h y) x))
        ≤ C * Work.Diff.STE.CSq (s + 2 * k - 1) (Work.Diff.STE.fourierCoeff h) := by
  classical
  -- ## Injectivity and invertibility of the differentials of `T`, `T'`
  have hinjT : Function.Injective T := fun x y hxy => by rw [← hTinv1 x, hxy, hTinv1 y]
  have hinjT' : Function.Injective T' := fun x y hxy => by rw [← hTinv2 x, hxy, hTinv2 y]
  have hdet_of : ∀ (A B : (ι → ℝ) →L[ℝ] (ι → ℝ)), A.comp B = 1 → B.det ≠ 0 := by
    intro A B hcomp hz
    have hinj : Function.Injective B := fun u v huv => by
      have h1 := congrArg (fun (L : (ι → ℝ) →L[ℝ] (ι → ℝ)) => L u) hcomp
      have h2 := congrArg (fun (L : (ι → ℝ) →L[ℝ] (ι → ℝ)) => L v) hcomp
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply] at h1 h2
      rw [huv] at h1
      exact h1.symm.trans h2
    have hz' : LinearMap.det ((B : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))) = 0 := hz
    exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hz') (by rw [LinearMap.ker_eq_bot]; exact hinj)
  have hdetT : ∀ z : ι → ℝ, (fderiv ℝ T z).det ≠ 0 := by
    intro z
    have hcomp : fderiv ℝ (fun x => T' (T x)) z = (fderiv ℝ T' (T z)).comp (fderiv ℝ T z) :=
      fderiv_comp z ((hT'.differentiable (by simp)).differentiableAt)
        ((hT.differentiable (by simp)).differentiableAt)
    have h1 : fderiv ℝ (fun x => T' (T x)) z = 1 := by
      rw [show (fun x : ι → ℝ => T' (T x)) = id from funext hTinv1]
      exact fderiv_id
    have h2 : (fderiv ℝ T' (T z)).comp (fderiv ℝ T z) = 1 := by rw [← hcomp]; exact h1
    exact hdet_of _ _ h2
  have hdetT' : ∀ z : ι → ℝ, (fderiv ℝ T' z).det ≠ 0 := by
    intro z
    have hcomp : fderiv ℝ (fun y => T (T' y)) z = (fderiv ℝ T (T' z)).comp (fderiv ℝ T' z) :=
      fderiv_comp z ((hT.differentiable (by simp)).differentiableAt)
        ((hT'.differentiable (by simp)).differentiableAt)
    have h1 : fderiv ℝ (fun y => T (T' y)) z = 1 := by
      rw [show (fun y : ι → ℝ => T (T' y)) = id from funext hTinv2]
      exact fderiv_id
    have h2 : (fderiv ℝ T (T' z)).comp (fderiv ℝ T' z) = 1 := by rw [← hcomp]; exact h1
    exact hdet_of _ _ h2
  -- ## The three certificates
  obtain ⟨C1, hC1nn, hC1b⟩ :=
    double_comm_conjLapPow_le ρ hρb hdiam L hL hρlip T T' hT hT' hTinv1 hTinv2 hTper
      (1 : (ι → ℝ) → ℂ) β contDiff_const (fun _ _ => rfl) hβ hβp k hk s
  obtain ⟨C2, hC2nn, hC2b⟩ :=
    Work.Diff.STE.B3.SymCalcStep6.conjLapPow_CSq_le T T' hT hT' hTper hTinv1 hTinv2
      hinjT hinjT' hdetT hdetT' k s
  obtain ⟨C3, hC3nn, hC3b⟩ :=
    flat_multiplier_gain ρ hρb hdiam hρ0 L hL hρlip β hβ hβp (s + 2 * k - 1)
  refine ⟨2 * (C1 + C2 * C3), by positivity, ?_⟩
  intro ε hε hε1 h hh hhp
  -- ## Abbreviations: the target `Wc`, the commutator `w` and the four-atom expression `Z`
  set Wc : (ι → ℝ) → ℂ := fun x => β x * Work.Diff.STE.B3.SymCalc.flatCut ρ ε
        (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' h) x
      - Work.Diff.STE.B3.SymCalc.flatCut ρ ε
        (fun y => β y * Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' h y) x with hWcdef
  set w : (ι → ℝ) → ℂ := fun x => β x * Work.Diff.STE.B3.SymCalc.flatCut ρ ε h x
      - Work.Diff.STE.B3.SymCalc.flatCut ρ ε (fun y => β y * h y) x with hwdef
  set Z : (ι → ℝ) → ℂ := fun x => (1 : (ι → ℝ) → ℂ) x * (
      (β x * (Work.Diff.STE.B3.SymCalc.flatCut ρ ε
          (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' h) x
        - Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T'
          (Work.Diff.STE.B3.SymCalc.flatCut ρ ε h) x))
    + (β x * Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T'
          (Work.Diff.STE.B3.SymCalc.flatCut ρ ε h) x
        - Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T'
          (fun y => β y * Work.Diff.STE.B3.SymCalc.flatCut ρ ε h y) x)
    - (Work.Diff.STE.B3.SymCalc.flatCut ρ ε
          (fun y => β y * Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' h y) x
        - Work.Diff.STE.B3.SymCalc.flatCut ρ ε
          (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T'
            (fun y => β y * h y)) x)
    - (Work.Diff.STE.B3.SymCalc.flatCut ρ ε
          (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T'
            (fun y => β y * h y)) x
        - Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T'
          (Work.Diff.STE.B3.SymCalc.flatCut ρ ε (fun y => β y * h y)) x)) with hZdef
  -- ## Smoothness and periodicity of the pieces
  have hPh_sm : ContDiff ℝ (⊤ : ℕ∞)
      (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' h) :=
    Work.Diff.STE.B3.SymCalcStep6.conjLapPow_contDiff T T' hT hT' hTper hTinv1 hTinv2 k hh hhp
  have hPh_p : Work.Diff.STE.Periodic1 (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' h) :=
    Work.Diff.STE.B3.SymCalcStep6.conjLapPow_periodic T T' hTper k h
  have hSh_sm : ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.B3.SymCalc.flatCut ρ ε h) :=
    Work.Diff.STE.B3.SymCalcStep1.flatCut_contDiff ρ hρb ε hh hhp
  have hSh_p : Work.Diff.STE.Periodic1 (Work.Diff.STE.B3.SymCalc.flatCut ρ ε h) :=
    Work.Diff.STE.B3.SymCalcStep1.flatCut_periodic ρ ε h
  have hβh_sm : ContDiff ℝ (⊤ : ℕ∞) (fun y : ι → ℝ => β y * h y) := hβ.mul hh
  have hβh_p : Work.Diff.STE.Periodic1 (fun y : ι → ℝ => β y * h y) :=
    Work.Diff.STE.B3.SymCalcStep1.Periodic1_mul' hβp hhp
  have hβPh_sm : ContDiff ℝ (⊤ : ℕ∞)
      (fun y : ι → ℝ => β y * Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' h y) :=
    hβ.mul hPh_sm
  have hβPh_p : Work.Diff.STE.Periodic1
      (fun y : ι → ℝ => β y * Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' h y) :=
    Work.Diff.STE.B3.SymCalcStep1.Periodic1_mul' hβp hPh_p
  have hPhflat_sm : ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.B3.SymCalc.flatCut ρ ε
      (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' h)) :=
    Work.Diff.STE.B3.SymCalcStep1.flatCut_contDiff ρ hρb ε hPh_sm hPh_p
  have hPhflat_p : Work.Diff.STE.Periodic1 (Work.Diff.STE.B3.SymCalc.flatCut ρ ε
      (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' h)) :=
    Work.Diff.STE.B3.SymCalcStep1.flatCut_periodic ρ ε _
  have hβPhflat_sm : ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.B3.SymCalc.flatCut ρ ε
      (fun y : ι → ℝ => β y * Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' h y)) :=
    Work.Diff.STE.B3.SymCalcStep1.flatCut_contDiff ρ hρb ε hβPh_sm hβPh_p
  have hβPhflat_p : Work.Diff.STE.Periodic1 (Work.Diff.STE.B3.SymCalc.flatCut ρ ε
      (fun y : ι → ℝ => β y * Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' h y)) :=
    Work.Diff.STE.B3.SymCalcStep1.flatCut_periodic ρ ε _
  have hShβ_sm : ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.B3.SymCalc.flatCut ρ ε
      (fun y : ι → ℝ => β y * h y)) :=
    Work.Diff.STE.B3.SymCalcStep1.flatCut_contDiff ρ hρb ε hβh_sm hβh_p
  have hw_sm : ContDiff ℝ (⊤ : ℕ∞) w := by
    rw [hwdef]
    exact (hβ.mul hSh_sm).sub hShβ_sm
  have hw_p : Work.Diff.STE.Periodic1 w := by
    rw [hwdef]
    exact Work.Diff.STE.B3.SymCalcStep1.Periodic1_sub'
      (Work.Diff.STE.B3.SymCalcStep1.Periodic1_mul' hβp hSh_p)
      (Work.Diff.STE.B3.SymCalcStep1.flatCut_periodic ρ ε _)
  have hPw_sm : ContDiff ℝ (⊤ : ℕ∞)
      (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' w) :=
    Work.Diff.STE.B3.SymCalcStep6.conjLapPow_contDiff T T' hT hT' hTper hTinv1 hTinv2 k hw_sm hw_p
  have hPw_p : Work.Diff.STE.Periodic1 (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' w) :=
    Work.Diff.STE.B3.SymCalcStep6.conjLapPow_periodic T T' hTper k w
  -- ## The `u − v` form of the additivity of `P_k`
  have hsub : Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' w
      = Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T'
          (fun x : ι → ℝ => β x * Work.Diff.STE.B3.SymCalc.flatCut ρ ε h x)
        - Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T'
          (Work.Diff.STE.B3.SymCalc.flatCut ρ ε (fun y : ι → ℝ => β y * h y)) := by
    rw [hwdef]
    exact conjLapPow_sub T T' hT' hTper hTinv1 hTinv2 k
      (u := fun x : ι → ℝ => β x * Work.Diff.STE.B3.SymCalc.flatCut ρ ε h x)
      (v := Work.Diff.STE.B3.SymCalc.flatCut ρ ε (fun y : ι → ℝ => β y * h y))
      (hβ.mul hSh_sm) hShβ_sm
      (Work.Diff.STE.B3.SymCalcStep1.Periodic1_mul' hβp hSh_p)
      (Work.Diff.STE.B3.SymCalcStep1.flatCut_periodic ρ ε _)
  -- ## The pointwise identity `Wc = Z + P_k w`
  have hId : Wc = fun x => Z x + Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' w x := by
    rw [hWcdef, hZdef]
    funext x
    rw [hsub]
    simp only [Pi.sub_apply, Pi.one_apply, one_mul]
    ring
  have hZ_eq : Z = fun x => Wc x - Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' w x := by
    rw [hZdef, hWcdef]
    funext x
    rw [hsub]
    simp only [Pi.sub_apply, Pi.one_apply, one_mul]
    ring
  -- ## Smoothness and periodicity of `Z`, via the identity
  have hZ_sm : ContDiff ℝ (⊤ : ℕ∞) Z := by
    rw [hZ_eq]
    exact ((hβ.mul hPhflat_sm).sub hβPhflat_sm).sub hPw_sm
  have hZ_p : Work.Diff.STE.Periodic1 Z := by
    rw [hZ_eq]
    exact Work.Diff.STE.B3.SymCalcStep1.Periodic1_sub'
      (Work.Diff.STE.B3.SymCalcStep1.Periodic1_sub'
        (Work.Diff.STE.B3.SymCalcStep1.Periodic1_mul' hβp hPhflat_p) hβPhflat_p) hPw_p
  -- ## The two bounds
  have hZbound : Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff Z)
      ≤ C1 * Work.Diff.STE.CSq (s + 2 * k - 1) (Work.Diff.STE.fourierCoeff h) := by
    rw [hZdef]
    exact hC1b ε hε hε1 h hh hhp
  have hPwbound : Work.Diff.STE.CSq s
        (Work.Diff.STE.fourierCoeff (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' w))
      ≤ (C2 * C3) * Work.Diff.STE.CSq (s + 2 * k - 1) (Work.Diff.STE.fourierCoeff h) := by
    have hlev : (s + 2 * k - 1) + 1 = s + 2 * k := by omega
    have h3 := hC3b ε hε hε1 h hh hhp
    rw [hlev] at h3
    calc Work.Diff.STE.CSq s
          (Work.Diff.STE.fourierCoeff (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' w))
        ≤ C2 * Work.Diff.STE.CSq (s + 2 * k) (Work.Diff.STE.fourierCoeff w) :=
          hC2b w hw_sm hw_p
      _ ≤ C2 * (C3 * Work.Diff.STE.CSq (s + 2 * k - 1) (Work.Diff.STE.fourierCoeff h)) :=
          mul_le_mul_of_nonneg_left h3 hC2nn
      _ = (C2 * C3) * Work.Diff.STE.CSq (s + 2 * k - 1)
            (Work.Diff.STE.fourierCoeff h) := by ring
  -- ## Assembly
  have hfc : Work.Diff.STE.fourierCoeff
        (fun x => Z x + Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' w x)
      = fun m : ι → ℤ => Work.Diff.STE.fourierCoeff Z m
          + Work.Diff.STE.fourierCoeff (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' w) m :=
    funext fun m => Work.Diff.STE.B3.SymCalcStep1.fourierCoeff_add_of_continuous Z _
      hZ_sm.continuous hPw_sm.continuous m
  have hsumZ := Work.Diff.STE.B3.SymCalcStep1.summable_CSq_fourierCoeff s hZ_sm hZ_p
  have hsumPw := Work.Diff.STE.B3.SymCalcStep1.summable_CSq_fourierCoeff s hPw_sm hPw_p
  calc Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff Wc)
      = Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff
          (fun x => Z x + Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' w x)) := by
        rw [hId]
    _ = Work.Diff.STE.CSq s (fun m : ι → ℤ => Work.Diff.STE.fourierCoeff Z m
          + Work.Diff.STE.fourierCoeff (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' w) m) := by
        rw [hfc]
    _ ≤ 2 * (Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff Z)
          + Work.Diff.STE.CSq s
              (Work.Diff.STE.fourierCoeff (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T' w))) :=
        Work.Diff.STE.B3.SymCalcStep1.CSq_add_le s _ _ hsumZ hsumPw
    _ ≤ 2 * (C1 * Work.Diff.STE.CSq (s + 2 * k - 1) (Work.Diff.STE.fourierCoeff h)
          + (C2 * C3) * Work.Diff.STE.CSq (s + 2 * k - 1)
              (Work.Diff.STE.fourierCoeff h)) := by
        refine mul_le_mul_of_nonneg_left (add_le_add hZbound hPwbound) (by norm_num)
    _ = (2 * (C1 + C2 * C3)) * Work.Diff.STE.CSq (s + 2 * k - 1)
          (Work.Diff.STE.fourierCoeff h) := by ring

/-- The `d`-mixed piece of the six-term decomposition of `pairOp`: `c·[V, M_d](Λ g)` with `V = conjCut ρ ε T T'` (order `0`) and `Λ = lapPow k` (order `2k`); the gain of `[V,M_d]` (order `−1`) must be taken before `Λ`.  Route: the operator identity `[V,M_d]Λ = Λ[V,M_d] + [[V,M_d],Λ]` applied to `g` splits into (i) `c·Λ([V,M_d]g)`, bounded by the `conjCut_multiplier_gain` certificate for `[M_d,V] = −[V,M_d]` instantiated at parameter `s+2k−1` (output level `s+2k`) followed by the order-`2k` cost of `Λ` (`(lapPow_toolbox k s).2.1`), and (ii) `c·([[V,M_d],Λ]g)`, expanded by `[[V,M_d],Λ] = [V,Λ]M_d + V[M_d,Λ] − M_d[V,Λ] − [M_d,Λ]V` into four terms bounded by `conj_cut_comm_lapPow_le` (`[Λ,V]`, applied to `g` and to `d·g`; `[V,Λ] = −[Λ,V]`), the flat Leibniz certificate `dB3_flat_comm_le` with the periodic multiplier `d` (`[M_d,Λ] = −[Λ,M_d]`, applied to `g` and to `V g`), and the order-`0` bound `conjCut_CSq_le` for `V`.  The pointwise identity relating `[[V,M_d],Λ]g` to that four-term sum uses the additivity of `Λ` and of `V` (`lapPow_algebra.2`, `conjLapPow_add`-style additivity of `flatCut` from `flatCut_fintype_sum` plus `compMap_add`), in the `u − v` form derived from `u = (u−v)+v`. -/
theorem mixed_piece_v_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : (ι → ℝ) → ℝ) (hρ : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1)
    (hdiam : ∀ y : ι → ℝ, 2 < ∑ i, (y i) ^ 2 → ρ y = 0)
    (hρ0 : ρ 0 = 1)
    (L : ℝ) (hL : 0 ≤ L) (hρlip : ∀ y z : ι → ℝ, ‖ρ y - ρ z‖ ≤ L * ‖y - z‖)
    (T T' : (ι → ℝ) → (ι → ℝ)) (hT : ContDiff ℝ (⊤ : ℕ∞) T) (hT' : ContDiff ℝ (⊤ : ℕ∞) T')
    (hTinv1 : ∀ x : ι → ℝ, T' (T x) = x) (hTinv2 : ∀ y : ι → ℝ, T (T' y) = y)
    (hTper : ∀ (i : ι) (x : ι → ℝ), T (x + Pi.single i 1) = T x + Pi.single i 1)
    (c d : (ι → ℝ) → ℂ) (hc : ContDiff ℝ (⊤ : ℕ∞) c) (hcp : Work.Diff.STE.Periodic1 c)
    (hd : ContDiff ℝ (⊤ : ℕ∞) d) (hdp : Work.Diff.STE.Periodic1 d)
    (k : ℕ) (hk : 1 ≤ k) (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (ε : ℝ), 0 < ε → ε ≤ 1 → ∀ g : (ι → ℝ) → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) g → Work.Diff.STE.Periodic1 g →
      Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (fun x => c x *
          (Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T'
              (fun y => d y * Work.Diff.STE.B3.SymCalcStep5.lapPow k g y) x
            - d x * Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T'
              (Work.Diff.STE.B3.SymCalcStep5.lapPow k g) x)))
        ≤ C * Work.Diff.STE.CSq (s + 2 * k - 1) (Work.Diff.STE.fourierCoeff g) := by
  classical
  -- ## Injectivity, periodicity and invertible differentials of `T`, `T'`
  have hT'per : ∀ (i : ι) (y : ι → ℝ), T' (y + Pi.single i 1) = T' y + Pi.single i 1 :=
    Work.Diff.STE.B3.SymCalcStep1.shift_T' T T' hTper hTinv1 hTinv2
  have hinjT : Function.Injective T := fun x y hxy => by rw [← hTinv1 x, hxy, hTinv1 y]
  have hinjT' : Function.Injective T' := fun x y hxy => by rw [← hTinv2 x, hxy, hTinv2 y]
  have hdet_of : ∀ (A B : (ι → ℝ) →L[ℝ] (ι → ℝ)), A.comp B = 1 → B.det ≠ 0 := by
    intro A B hcomp hz
    have hinj : Function.Injective B := fun u v huv => by
      have h1 := congrArg (fun (L : (ι → ℝ) →L[ℝ] (ι → ℝ)) => L u) hcomp
      have h2 := congrArg (fun (L : (ι → ℝ) →L[ℝ] (ι → ℝ)) => L v) hcomp
      simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.one_apply] at h1 h2
      rw [huv] at h1
      exact h1.symm.trans h2
    have hz' : LinearMap.det ((B : (ι → ℝ) →ₗ[ℝ] (ι → ℝ))) = 0 := hz
    exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hz') (by rw [LinearMap.ker_eq_bot]; exact hinj)
  have hdetT : ∀ z : ι → ℝ, (fderiv ℝ T z).det ≠ 0 := by
    intro z
    have hcomp : fderiv ℝ (fun x => T' (T x)) z = (fderiv ℝ T' (T z)).comp (fderiv ℝ T z) :=
      fderiv_comp z ((hT'.differentiable (by simp)).differentiableAt)
        ((hT.differentiable (by simp)).differentiableAt)
    have h1 : fderiv ℝ (fun x => T' (T x)) z = 1 := by
      rw [show (fun x : ι → ℝ => T' (T x)) = id from funext hTinv1]
      exact fderiv_id
    have h2 : (fderiv ℝ T' (T z)).comp (fderiv ℝ T z) = 1 := by rw [← hcomp]; exact h1
    exact hdet_of _ _ h2
  have hdetT' : ∀ z : ι → ℝ, (fderiv ℝ T' z).det ≠ 0 := by
    intro z
    have hcomp : fderiv ℝ (fun y => T (T' y)) z = (fderiv ℝ T (T' z)).comp (fderiv ℝ T' z) :=
      fderiv_comp z ((hT.differentiable (by simp)).differentiableAt)
        ((hT'.differentiable (by simp)).differentiableAt)
    have h1 : fderiv ℝ (fun y => T (T' y)) z = 1 := by
      rw [show (fun y : ι → ℝ => T (T' y)) = id from funext hTinv2]
      exact fderiv_id
    have h2 : (fderiv ℝ T (T' z)).comp (fderiv ℝ T' z) = 1 := by rw [← hcomp]; exact h1
    exact hdet_of _ _ h2
  -- ## The certificates
  have hβ : ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.B3.SymCalc.compMap T d) := hd.comp hT
  have hβp : Work.Diff.STE.Periodic1 (Work.Diff.STE.B3.SymCalc.compMap T d) := by
    intro i x
    show d (T (x + Pi.single i 1)) = d (T x)
    rw [hTper i x]
    exact hdp i (T x)
  obtain ⟨Ccore, hCcore_nn, hCcore⟩ :=
    mixed_core_le ρ hρ hdiam hρ0 L hL hρlip T T' hT hT' hTinv1 hTinv2 hTper
      (Work.Diff.STE.B3.SymCalc.compMap T d) hβ hβp k hk s
  obtain ⟨Cc, hCc_nn, hCc⟩ := mul_CSq_le s c hc hcp
  obtain ⟨Ca, hCa_nn, hCa⟩ :=
    Work.Diff.STE.B3.SymCalcStep1.fourierCoeff_comp_le s T' hT' hT'per hinjT' hdetT'
  obtain ⟨Cb, hCb_nn, hCb⟩ :=
    Work.Diff.STE.B3.SymCalcStep1.fourierCoeff_comp_le (s + 2 * k - 1) T hT hTper hinjT hdetT
  refine ⟨Cc * Ca * Ccore * Cb, by positivity, ?_⟩
  intro ε hε hε1 g hg hgp
  -- ## The transported core function
  set W : (ι → ℝ) → ℂ := fun x => Work.Diff.STE.B3.SymCalc.compMap T d x *
        Work.Diff.STE.B3.SymCalc.flatCut ρ ε
          (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T'
            (Work.Diff.STE.B3.SymCalc.compMap T g)) x
      - Work.Diff.STE.B3.SymCalc.flatCut ρ ε
          (fun y => Work.Diff.STE.B3.SymCalc.compMap T d y *
            Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T'
              (Work.Diff.STE.B3.SymCalc.compMap T g) y) x with hWdef
  have hgT_sm : ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.B3.SymCalc.compMap T g) := hg.comp hT
  have hgT_p : Work.Diff.STE.Periodic1 (Work.Diff.STE.B3.SymCalc.compMap T g) := by
    intro i x
    show g (T (x + Pi.single i 1)) = g (T x)
    rw [hTper i x]
    exact hgp i (T x)
  have hPh_sm : ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T'
      (Work.Diff.STE.B3.SymCalc.compMap T g)) :=
    Work.Diff.STE.B3.SymCalcStep6.conjLapPow_contDiff T T' hT hT' hTper hTinv1 hTinv2 k
      hgT_sm hgT_p
  have hPh_p : Work.Diff.STE.Periodic1 (Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T'
      (Work.Diff.STE.B3.SymCalc.compMap T g)) :=
    Work.Diff.STE.B3.SymCalcStep6.conjLapPow_periodic T T' hTper k _
  have hW_sm : ContDiff ℝ (⊤ : ℕ∞) W := by
    rw [hWdef]
    exact (hβ.mul (Work.Diff.STE.B3.SymCalcStep1.flatCut_contDiff
        (g := Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T'
          (Work.Diff.STE.B3.SymCalc.compMap T g)) ρ hρ ε hPh_sm hPh_p)).sub
      (Work.Diff.STE.B3.SymCalcStep1.flatCut_contDiff
        (g := fun y : ι → ℝ => Work.Diff.STE.B3.SymCalc.compMap T d y *
          Work.Diff.STE.B3.SymCalcStep5.conjLapPow k T T'
            (Work.Diff.STE.B3.SymCalc.compMap T g) y)
        ρ hρ ε (hβ.mul hPh_sm) (Work.Diff.STE.B3.SymCalcStep1.Periodic1_mul' hβp hPh_p))
  have hW_p : Work.Diff.STE.Periodic1 W := by
    rw [hWdef]
    exact Work.Diff.STE.B3.SymCalcStep1.Periodic1_sub'
      (Work.Diff.STE.B3.SymCalcStep1.Periodic1_mul' hβp
        (Work.Diff.STE.B3.SymCalcStep1.flatCut_periodic ρ ε _))
      (Work.Diff.STE.B3.SymCalcStep1.flatCut_periodic ρ ε _)
  -- ## The bound on `W`
  have hWbound : Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff W)
      ≤ Ccore * Work.Diff.STE.CSq (s + 2 * k - 1)
          (Work.Diff.STE.fourierCoeff (Work.Diff.STE.B3.SymCalc.compMap T g)) := by
    rw [hWdef]
    exact hCcore ε hε hε1 (Work.Diff.STE.B3.SymCalc.compMap T g) hgT_sm hgT_p
  -- ## The transport identity
  have hid := mixed_transport_identity ρ ε T T' hTinv1 hTinv2 d g k
  have htarget : (fun x => c x *
        (Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T'
            (fun y => d y * Work.Diff.STE.B3.SymCalcStep5.lapPow k g y) x
          - d x * Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T'
            (Work.Diff.STE.B3.SymCalcStep5.lapPow k g) x))
      = fun x => - (c x * Work.Diff.STE.B3.SymCalc.compMap T' W x) := by
    funext x
    have hx := congrFun hid x
    rw [hWdef]
    rw [← hx]
    ring
  -- ## Smoothness and periodicity of the transported function
  have hcompTW_sm : ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.B3.SymCalc.compMap T' W) := hW_sm.comp hT'
  have hcompTW_p : Work.Diff.STE.Periodic1 (Work.Diff.STE.B3.SymCalc.compMap T' W) := by
    intro i x
    show W (T' (x + Pi.single i 1)) = W (T' x)
    rw [hT'per i x]
    exact hW_p i (T' x)
  -- ## Assembly
  calc Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (fun x => c x *
        (Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T'
            (fun y => d y * Work.Diff.STE.B3.SymCalcStep5.lapPow k g y) x
          - d x * Work.Diff.STE.B3.SymCalc.conjCut ρ ε T T'
            (Work.Diff.STE.B3.SymCalcStep5.lapPow k g) x)))
      = Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff
          (fun x => c x * Work.Diff.STE.B3.SymCalc.compMap T' W x)) := by
        rw [htarget]
        exact Work.Diff.STE.B3.SymCalcStep6.CSq_fourierCoeff_neg s _
    _ ≤ Cc * Work.Diff.STE.CSq s
          (Work.Diff.STE.fourierCoeff (Work.Diff.STE.B3.SymCalc.compMap T' W)) :=
        hCc _ hcompTW_sm hcompTW_p
    _ ≤ Cc * (Ca * Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff W)) :=
        mul_le_mul_of_nonneg_left (hCa W hW_sm hW_p) hCc_nn
    _ ≤ Cc * (Ca * (Ccore * Work.Diff.STE.CSq (s + 2 * k - 1)
          (Work.Diff.STE.fourierCoeff (Work.Diff.STE.B3.SymCalc.compMap T g)))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hWbound hCa_nn) hCc_nn
    _ ≤ Cc * (Ca * (Ccore * (Cb * Work.Diff.STE.CSq (s + 2 * k - 1)
          (Work.Diff.STE.fourierCoeff g)))) := by
        refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left ?_ hCcore_nn) hCa_nn) hCc_nn
        exact hCb g hg hgp
    _ = (Cc * Ca * Ccore * Cb) * Work.Diff.STE.CSq (s + 2 * k - 1)
          (Work.Diff.STE.fourierCoeff g) := by ring

end Work.Diff.STE.B3.SymCalcStep7
