import Mathlib
import Submission.Work.EQ.DefsCore
import Submission.Work.EQ.CycleDefs
import Submission.Work.EQ.chain_eq_candChain_of_tails
import Submission.Work.EQ.fan_trichotomy
import Submission.Work.EQ.charVal_props
import Submission.Work.EQ.charVal_set
import Submission.Work.EQ.H0_regular_aux

/-!
# Auxiliary lemmas for step 5 (the covering step) of `Work.EQ.H0_regular`

This module collects the elementary facts the covering argument (Rychlik Theorem 11,
equations (140)–(141)) needs, plus a named packaging of Rychlik's Theorem 7 trichotomy:

* `FanTrich a h δ` — the trichotomy predicate of `Work.EQ.fan_trichotomy` at radius `δ`;
* `fan_trichotomy'` — `∃ δ > 0, FanTrich a h δ`;
* `psi_hShift`, `psi_shiftZ` — the invariant parameter `ψ = ψ₁ψ₂` is invariant under the shift
  `σ` (this is the reason the shifted cluster points of a good ray all have `ψ`-value `c₀`);
* `fan_append_true`, `fan_append_replicate_true` — appending principal letters (`true`) to a fan
  word does not change the fan map (a chain whose tail is principal beyond depth `N` can be read at
  any depth `≥ N`);
* `exists_candChain_of_mem_H0` — every chain of `H0` is an explicit `candChain` at its own tail
  depth (the "reading" of Rychlik Theorem 8);
* `psi_candChain` — the invariant parameter of a candidate chain is its value `c`.
-/

noncomputable section

open Filter _root_.Topology Complex Metric

namespace Work.EQ

/-! ## The trichotomy of Rychlik's Theorem 7 as a named predicate -/

/-- **Rychlik's Theorem 7(2)(3) at radius `δ`.**  For every sequence of branch words there is a
subsequence on which one of the following holds:

* (i) all the fan maps agree with the fan map of one fixed word on the ball `B(0,δ)`;
* (ii) the words are `ε₀ ++ true^{s k} ++ C k` with `s k → ∞`, each `C k` a returning word with a
  common characteristic value `μ = charVal ε₁ ∈ M`, and the fan maps converge uniformly on
  `B(0,δ)` to `fan ε₀ (μ ·)`;
* (iii) the fan maps shrink to the axis (the "flattening" case, refuted by
  `Work.EQ.LaNnas.no_near_axis_segment` in the applications). -/
def FanTrich (a : ℝ) (h : ℂ → ℂ) (δ : ℝ) : Prop :=
  ∀ ε : ℕ → List Bool, ∃ φ : ℕ → ℕ, StrictMono φ ∧
    ((∃ ε₀ : List Bool, ∀ k, Set.EqOn (fan a h (ε (φ k))) (fan a h ε₀) (Metric.ball 0 δ)) ∨
     (∃ (ε₀ ε₁ : List Bool) (s : ℕ → ℕ) (C : ℕ → List Bool),
        Tendsto s atTop atTop ∧
        (∀ k, ε (φ k) = ε₀ ++ List.replicate (s k) true ++ C k) ∧
        (∀ k, fan a h (C k) 0 = ((-1 / 2 : ℂ), (0 : ℂ)) ∧
          charVal a h (C k) = charVal a h ε₁) ∧
        fan a h ε₁ 0 = ((-1 / 2 : ℂ), (0 : ℂ)) ∧
        (charVal a h ε₁).im = 0 ∧ 0 < (charVal a h ε₁).re ∧ (charVal a h ε₁).re < 1 ∧
        TendstoUniformlyOn (fun k => fan a h (ε (φ k)))
          (fun u => fan a h ε₀ (charVal a h ε₁ * u)) atTop (Metric.ball 0 δ)) ∨
     ((∀ n : ℕ, ∀ᶠ k in atTop, n ≤ nonA1Count a h (ε (φ k))) ∧
        ∀ η : ℝ, 0 < η → ∀ᶠ k in atTop, ∀ u ∈ Metric.ball (0 : ℂ) δ,
          ‖(fan a h (ε (φ k)) u).1 - (fan a h (ε (φ k)) 0).1‖ < η ∧
          ‖(fan a h (ε (φ k)) u).2‖ < η * ‖(fan a h (ε (φ k)) u).1 - ((a / 2 : ℝ) : ℂ)‖))

/-- **Rychlik's Theorem 7(2)(3), packaged.**  There is a radius at which the trichotomy holds. -/
theorem fan_trichotomy' {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {r : ℝ}
    (hh : IsStableGerm a h r) :
    ∃ δ : ℝ, 0 < δ ∧ FanTrich a h δ := by
  obtain ⟨δ, hδ, h⟩ := fan_trichotomy ha0 ha1 hh
  exact ⟨δ, hδ, h⟩

/-! ## `ψ` is invariant under the shift -/

/-- `eqLam a ≠ 0` for `0 < a < 1`. -/
private theorem eqLamC_ne_zero {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : ((eqLam a : ℝ) : ℂ) ≠ 0 := by
  rw [← Complex.ofReal_zero, Ne, Complex.ofReal_inj]
  exact ne_of_gt (eqLam_pos' ha0 ha1)

/-- **The invariant parameter is invariant under the shift.**  `ψ (σ p) = ψ p` for
`σ = hShift a`, i.e. `λ ψ₁ · (ψ₂ / λ) = ψ₁ ψ₂`. -/
theorem psi_hShift {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (p : ChainData) :
    psi (hShift a p) = psi p := by
  have hlam := eqLamC_ne_zero ha0 ha1
  simp only [psi, hShift]
  field_simp

/-- The same for the integer shifts `σ^j = shiftZ a j`. -/
theorem psi_shiftZ {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (j : ℤ) (p : ChainData) :
    psi (shiftZ a j p) = psi p := by
  have hlam := eqLamC_ne_zero ha0 ha1
  simp only [psi, shiftZ]
  have hz : ((eqLam a : ℝ) : ℂ) ^ j ≠ 0 := zpow_ne_zero j hlam
  field_simp

/-! ## Appending principal letters does not change a fan map -/

/-- **Appending one principal letter.**  If the principal branch inverts the germ along the
stable manifold (`invBranch true ∘ germC ∘ (λ·) = germC`), then appending a `true` at the *end* of
a word does not change the fan map.  (Consequently the fan word of a chain may be read at any
depth beyond the depth from which its tail is principal.) -/
theorem fan_append_true {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {δ : ℝ}
    (hinv : ∀ u : ℂ, ‖u‖ < δ →
      invBranch a true (germC a h ((eqLam a : ℂ) * u)) = germC a h u)
    (l : List Bool) {u : ℂ} (hu : ‖u‖ < δ) :
    fan a h (l ++ [true]) u = fan a h l u := by
  induction l generalizing u with
  | nil => simp only [List.nil_append, fan]; exact hinv u hu
  | cons s l ih =>
    have hl0 : 0 < eqLam a := eqLam_pos' ha0 ha1
    have hl1 : eqLam a < 1 := eqLam_lt_one' ha0 ha1
    have hu' : ‖((eqLam a : ℝ) : ℂ) * u‖ < δ := by
      rw [norm_mul, show ‖((eqLam a : ℝ) : ℂ)‖ = |eqLam a| from by simp, abs_of_pos hl0]
      calc eqLam a * ‖u‖ ≤ 1 * ‖u‖ := by
            exact mul_le_mul_of_nonneg_right (le_of_lt hl1) (norm_nonneg u)
        _ = ‖u‖ := one_mul _
        _ < δ := hu
    simp only [List.cons_append, fan]
    rw [ih hu']

/-- **Appending several principal letters.**  Version of `fan_append_true` for
`List.replicate k true`. -/
theorem fan_append_replicate_true {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ} {δ : ℝ}
    (hinv : ∀ u : ℂ, ‖u‖ < δ →
      invBranch a true (germC a h ((eqLam a : ℂ) * u)) = germC a h u)
    (l : List Bool) (k : ℕ) {u : ℂ} (hu : ‖u‖ < δ) :
    fan a h (l ++ List.replicate k true) u = fan a h l u := by
  induction k generalizing l with
  | zero => simp
  | succ k ih =>
    rw [List.replicate_succ, ← List.singleton_append, ← List.append_assoc,
      ih (l ++ [true]), fan_append_true ha0 ha1 hinv l hu]

/-! ## Reading a chain off its tail -/

/-- **Every chain of `⁰H` is an explicit candidate chain.**  A chain of `H0` has both tails
principal from some depth `N`; reading it at that depth (`Work.EQ.chain_eq_candChain_of_tails`)
exhibits it as `candChain a h ε η s N (ψ₁ψ₂) ψ₁`. -/
theorem exists_candChain_of_mem_H0 {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ}
    {p : ChainData} (hp : p ∈ H0 a h) :
    ∃ (ε η s : List Bool) (N : ℕ), ε.length = N ∧ η.length = N ∧ s.length = N ∧
      p = candChain a h ε η s N (p.2.1 * p.2.2) p.2.1 := by
  obtain ⟨ε, hε, f, -, hf0, hfam⟩ := hp
  have hmem : p.2.1 ∈ Metric.ball p.2.1 ε := by
    rw [Metric.mem_ball, dist_self]; exact hε
  have hchain : IsChain a h p := by
    rw [← hf0]
    exact (hfam p.2.1 hmem).1
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp hchain.2.2.2.1
  obtain ⟨N₂, hN₂⟩ := eventually_atTop.mp hchain.2.2.2.2
  obtain ⟨ε', η', s', hε', hη', hs', heq⟩ :=
    chain_eq_candChain_of_tails ha0 ha1 hchain rfl
      (fun n hn => hN₁ n (le_trans (le_max_left _ _) hn))
      (fun n hn => hN₂ n (le_trans (le_max_right _ _) hn))
  exact ⟨ε', η', s', max N₁ N₂, hε', hη', hs', heq⟩

/-- The invariant parameter of a candidate chain is its value `c`. -/
theorem psi_candChain {a : ℝ} {h : ℂ → ℂ} (ε η s : List Bool) (N : ℕ) (c : ℂ) {z : ℂ}
    (hz : z ≠ 0) :
    (candChain a h ε η s N c z).2.1 * (candChain a h ε η s N c z).2.2 = c := by
  simp only [candChain_psi1, candChain_psi2]
  exact mul_div_cancel₀ c hz

end Work.EQ
