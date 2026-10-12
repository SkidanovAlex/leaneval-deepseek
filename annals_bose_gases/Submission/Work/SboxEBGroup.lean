import ChallengeDeps
import Submission.Work.SboxEB
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The FS group decomposition in the corpus e_B language

With `eB N s μ v h` (the `N`-particle ground energy at the fixed chemical
potential `μ` over the centred box `abox N s`) and its pairwise
superadditivity `eB_superadd_chosen` (SboxEB), this module closes the FS
group-trick spine (thm:smallbox proof, final_v2.tex ~3966–3972):

    e_B(n, μ) ≥ m·e_B(n′, μ) + e_B(n″, μ)          (n = m·n′ + n″)

i.e. **`eB_group_superadd_chosen`**:
`(m : ℝ)·eB n′ + eB n″ ≤ eB (m·n′ + n″)` for every `m n′ n″` (chosen-branch
hypotheses, `0 < μ`), together with the zero-particle base `eB 0 = 0`
(`eB_zero`) and the single-group repetition `eB_repeat_mul`
(`(m : ℝ)·eB n′ ≤ eB (m·n′)`).

The per-group *spectral content* (FS eq:SmallsimpleQs/A₀ +
eq:simpleaprioribog/eq:refinedaprioribog at FS precision, the count-universal
per-group bounds for `n′` with density `u′ := n′/s³ ∈ [C_n μ, (C_n+1)μ)`) is
the next, still-open layer — see the design note; the present module is its
formal consumer (the decomposition side, sorry-free and machine-checked).
-/

set_option linter.style.haveILetI false

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators

namespace Submission

open _root_.BoseGases
set_option autoImplicit false

namespace BoseGases

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The zero-particle small-box energy vanishes for every state. -/
lemma sboxE_zero (s μ : ℝ) (w w1 : ℝ³ → ℝ³ → ℝ) (Φ : X 0 → ℝ) :
    sboxE 0 s μ w w1 Φ = 0 := by
  unfold sboxE
  rw [qLHSword_eq_integral_qLHSden (N := 0)]
  have hd : ∀ x : X 0, qLHSden 0 s μ w w1 x = 0 := by
    intro x
    simp [qLHSden, pairSet]
  simp [kinWord]
  calc
    (∫ x in abox 0 s, (Φ x) ^ 2 * qLHSden 0 s μ w w1 x) = ∫ x in abox 0 s, (0 : ℝ) := by
      apply integral_congr_ae
      filter_upwards with x
      rw [hd x]
      ring
    _ = 0 := by simp

/-- The zero-particle ground energy is zero (independent of the branch data,
only the existence witness `h` and `0 < s` are needed to type/justify it). -/
lemma eB_zero {s μ : ℝ} (v : ℝ³ → ℝ)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v) (hs : 0 < s) :
    eB 0 s μ v h = 0 := by
  letI : Nonempty (CSBox 0 s) := nonempty_CSBox 0 hs
  unfold eB
  have hq : ∀ Φ : CSBox 0 s,
      (sboxE 0 s μ (wPairC s v) (wPairC s (g0 v h)) (Φ : X 0 → ℝ)) /
        (∫ x in abox 0 s, ((Φ : X 0 → ℝ) x) ^ 2) = 0 := by
    intro Φ
    rw [sboxE_zero s μ (wPairC s v) (wPairC s (g0 v h)) (Φ : X 0 → ℝ)]
    simp
  have hf : (fun Φ : CSBox 0 s =>
        (sboxE 0 s μ (wPairC s v) (wPairC s (g0 v h)) (Φ : X 0 → ℝ)) /
          (∫ x in abox 0 s, ((Φ : X 0 → ℝ) x) ^ 2))
      = fun _ : CSBox 0 s => (0 : ℝ) := funext hq
  calc
    (⨅ Φ : CSBox 0 s,
        (sboxE 0 s μ (wPairC s v) (wPairC s (g0 v h)) (Φ : X 0 → ℝ)) /
          (∫ x in abox 0 s, ((Φ : X 0 → ℝ) x) ^ 2))
        = (⨅ Φ : CSBox 0 s, (0 : ℝ)) := by rw [hf]
    _ = 0 := ciInf_const

/-- **The FS group-decomposition spine**: for the decomposition
`n = m·n′ + n″` of the particle number into `m` groups of `n′` and a
remainder `n″`, the ground energy dominates the sum of the per-group ground
energies (superadditivity iterated `m` times):

    eB (m·n′ + n″) ≥ (m : ℝ)·eB n′ + eB n″ . -/
lemma eB_group_superadd_chosen {m n' n'' : ℕ} {s R μ : ℝ} {v : ℝ³ → ℝ}
    (hR : 0 < R) (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hs : 0 < s) (hRs : R ≤ s * chiR0) (hμ : 0 < μ) :
    (m : ℝ) * eB n' s μ v h + eB n'' s μ v h ≤ eB (m * n' + n'') s μ v h := by
  induction m with
  | zero =>
      simp
  | succ m ih =>
      have hn : (m + 1) * n' + n'' = (m * n' + n'') + n' := by ring
      have hsa := eB_superadd_chosen (N1 := m * n' + n'') (N2 := n')
        hR hv_nonneg hvrad hv_memL1 hv_supp h hs hRs hμ
      have hc : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by norm_num [Nat.cast_add]
      have hl : ((m + 1 : ℕ) : ℝ) * eB n' s μ v h + eB n'' s μ v h
          = (m : ℝ) * eB n' s μ v h + eB n'' s μ v h + eB n' s μ v h := by
        rw [hc]
        ring
      rw [hl, hn]
      nlinarith [ih, hsa]

/-- Repetition of one group: `(m : ℝ)·eB n′ ≤ eB (m·n′)` (the `n″ = 0`
case of the group decomposition; feeds the `m` bulk groups of FS). -/
lemma eB_repeat_mul_chosen {m n' : ℕ} {s R μ : ℝ} {v : ℝ³ → ℝ}
    (hR : 0 < R) (hv_nonneg : 0 ≤ v) (hvrad : IsRadial v) (hv_memL1 : MemLp v 1)
    (hv_supp : tsupport v ⊆ ball (0 : ℝ³) R)
    (h : ∃ w : ℝ³ → ℝ, IsRadial w ∧ IsScatteringSolution w v)
    (hs : 0 < s) (hRs : R ≤ s * chiR0) (hμ : 0 < μ) :
    (m : ℝ) * eB n' s μ v h ≤ eB (m * n') s μ v h := by
  have hg := eB_group_superadd_chosen (m := m) (n' := n') (n'' := 0)
    hR hv_nonneg hvrad hv_memL1 hv_supp h hs hRs hμ
  have hz : eB 0 s μ v h = 0 := eB_zero v h hs
  rw [hz, add_zero] at hg
  simpa [mul_comm] using hg

end BoseGases

end Submission
