import Mathlib
import Submission.Work.EQ.CycleDefs
import Submission.Work.EQ.ChainReading
import Submission.Work.EQ.chain_eq_candChain_of_tails
import Submission.Work.EQ.H0_invParam_ge
import Submission.Work.EQ.StableTailDefs
import Submission.Work.EQ.backward_puiseux
import Submission.Work.EQ.exists_finset_zpow_annulus
import Submission.Work.EQ.component_shiftZ_invariant
import Submission.Work.EQ.AnnulusCover
import Submission.Work.EQ.H0_structure
import Submission.Work.EQ.germC_facts
import Submission.Work.EQ.bp_aux

namespace Work.EQ

open Complex Filter _root_.Topology
open scoped Topology

noncomputable section

/-! ## Words of length `N` -/

/-- The word of length `N` attached to a sign function `Fin N → Bool`. -/
def wordOf {N : ℕ} (f : Fin N → Bool) : List Bool := List.ofFn f

@[simp] theorem wordOf_length {N : ℕ} (f : Fin N → Bool) : (wordOf f).length = N :=
  List.length_ofFn

/-- Every word of length `N` is `wordOf f` for a sign function `f`. -/
theorem exists_wordOf_eq {N : ℕ} {l : List Bool} (hl : l.length = N) :
    ∃ f : Fin N → Bool, wordOf f = l := by
  subst hl
  exact ⟨fun i => l.get i, List.ofFn_get l⟩

/-! ## The `ψ₁`-fibre over the annulus is contained in finitely many candidate chains -/

/-- **Every chain of `S` over the annulus is one of the finitely many candidate chains.**

This is `chain_eq_candChain_of_tails` with the words repackaged as sign functions of length `N`
(so that the candidates form a finite family). -/
theorem mem_fibre_eq_candChain {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ}
    {S : Set ChainData} {c : ℂ} (hS : S ⊆ H0 a h) (hval : ∀ q ∈ S, q.2.1 * q.2.2 = c)
    {r₁ r₂ : ℝ} {N : ℕ}
    (htail : ∀ q ∈ S, q.2.1 ∈ Ann r₁ r₂ →
        (∀ n : ℕ, N ≤ n → q.1 (n : ℤ) = germC a h (((eqLam a : ℝ) : ℂ) ^ n * q.2.1)) ∧
        (∀ n : ℕ, N ≤ n → q.1 (-(n : ℤ)) = ugermC a h (((eqLam a : ℝ) : ℂ) ^ n * q.2.2)))
    {q : ChainData} (hq : q ∈ S) (hqA : q.2.1 ∈ Ann r₁ r₂) :
    ∃ (f g s : Fin N → Bool), q = candChain a h (wordOf f) (wordOf g) (wordOf s) N c q.2.1 := by
  obtain ⟨hfw, hbw⟩ := htail q hq hqA
  have hchain := isChain_of_mem_H0 (hS hq)
  obtain ⟨ε, η, s', hεl, hηl, hsl, hqeq⟩ :=
    chain_eq_candChain_of_tails ha0 ha1 hchain (hval q hq) hfw hbw
  obtain ⟨f, hf⟩ := exists_wordOf_eq hεl
  obtain ⟨g, hg⟩ := exists_wordOf_eq hηl
  obtain ⟨s, hs⟩ := exists_wordOf_eq hsl
  exact ⟨f, g, s, by rw [hf, hg, hs]; exact hqeq⟩

/-- **The `ψ₁`-fibre of `S` over a point of the annulus is finite.**

The fibre is contained in the images of the finitely many candidate chains at that point. -/
theorem fibre_finite_of_annulus {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {h : ℂ → ℂ}
    {S : Set ChainData} {c : ℂ} (hS : S ⊆ H0 a h) (hval : ∀ q ∈ S, q.2.1 * q.2.2 = c)
    {r₁ r₂ : ℝ} {N : ℕ}
    (htail : ∀ q ∈ S, q.2.1 ∈ Ann r₁ r₂ →
        (∀ n : ℕ, N ≤ n → q.1 (n : ℤ) = germC a h (((eqLam a : ℝ) : ℂ) ^ n * q.2.1)) ∧
        (∀ n : ℕ, N ≤ n → q.1 (-(n : ℤ)) = ugermC a h (((eqLam a : ℝ) : ℂ) ^ n * q.2.2)))
    {z : ℂ} (hz : z ∈ Ann r₁ r₂) :
    {q | q ∈ S ∧ q.2.1 = z}.Finite := by
  have himg : ((fun w : (Fin N → Bool) × (Fin N → Bool) × (Fin N → Bool) =>
        candChain a h (wordOf w.1) (wordOf w.2.1) (wordOf w.2.2) N c z) ''
        (Set.univ : Set ((Fin N → Bool) × (Fin N → Bool) × (Fin N → Bool)))).Finite :=
    (Set.toFinite _).image _
  refine himg.subset ?_
  rintro q ⟨hqS, hqz⟩
  obtain ⟨f, g, s, hqeq⟩ := mem_fibre_eq_candChain ha0 ha1 hS hval htail hqS (hqz ▸ hz)
  exact ⟨(f, g, s), Set.mem_univ _, by rw [hqeq, hqz]⟩

end

end Work.EQ

namespace Work.EQ

open Complex Filter _root_.Topology

noncomputable section

/-! ## The glued F3 families -/

/-- The depth-`dep` F3 end function: `u ↦ germC a h (λ^dep · u)`. -/
def endFun (a : ℝ) (h : ℂ → ℂ) (dep : ℕ) : ℂ → ℂ × ℂ :=
  fun u => germC a h (((eqLam a : ℝ) : ℂ) ^ dep * u)


/-- **The chain glued from the depth-`dep` F3 family `σ`.**  At parameter `t` (with
`ψ₁ = z₀ + t^(2^(2*dep))`) the middle segment of the chain is the F3 backward chain
`branchPt a (endFun a h dep) z₀ 1 σ` of length `2*dep` ending at `germC a h (λ^dep ψ₁)`; outside
the middle the chain follows the principal leaves: `germC` forward and `ugermC` backward. -/
def tailGlue (a : ℝ) (h : ℂ → ℂ) (cc z₀ : ℂ) (dep : ℕ) (σ : Fin (2 * dep) → Bool) (t : ℂ) :
    ChainData :=
  (fun j : ℤ =>
      if h1 : (dep : ℤ) ≤ j then
        germC a h (((eqLam a : ℝ) : ℂ) ^ j * (z₀ + t ^ (2 ^ (2 * dep))))
      else if h2 : -((dep : ℤ)) ≤ j then
        branchPt a (endFun a h dep) z₀ 1 σ t
          ⟨(j + (dep : ℤ)).toNat, by
            have h1' : ¬ ((dep : ℤ) ≤ j) := h1
            have h2' : -((dep : ℤ)) ≤ j := h2
            omega⟩
      else
        ugermC a h (((eqLam a : ℝ) : ℂ) ^ (-j) * (cc / (z₀ + t ^ (2 ^ (2 * dep))))),
    z₀ + t ^ (2 ^ (2 * dep)), cc / (z₀ + t ^ (2 ^ (2 * dep))))

@[simp] theorem tailGlue_psi1 (a : ℝ) (h : ℂ → ℂ) (cc z₀ : ℂ) (dep : ℕ)
    (σ : Fin (2 * dep) → Bool) (t : ℂ) :
    (tailGlue a h cc z₀ dep σ t).2.1 = z₀ + t ^ (2 ^ (2 * dep)) := rfl

@[simp] theorem tailGlue_psi2 (a : ℝ) (h : ℂ → ℂ) (cc z₀ : ℂ) (dep : ℕ)
    (σ : Fin (2 * dep) → Bool) (t : ℂ) :
    (tailGlue a h cc z₀ dep σ t).2.2 = cc / (z₀ + t ^ (2 ^ (2 * dep))) := rfl

/-- The forward tail of the glued family. -/
theorem tailGlue_fwd {a : ℝ} {h : ℂ → ℂ} {cc z₀ : ℂ} {dep : ℕ} {σ : Fin (2 * dep) → Bool}
    {t : ℂ} {j : ℤ} (hj : (dep : ℤ) ≤ j) :
    (tailGlue a h cc z₀ dep σ t).1 j =
      germC a h (((eqLam a : ℝ) : ℂ) ^ j * (z₀ + t ^ (2 ^ (2 * dep)))) := by
  simp only [tailGlue]
  rw [dif_pos hj]

/-- The backward tail of the glued family. -/
theorem tailGlue_bwd {a : ℝ} {h : ℂ → ℂ} {cc z₀ : ℂ} {dep : ℕ} {σ : Fin (2 * dep) → Bool}
    {t : ℂ} {j : ℤ} (hj : j < -((dep : ℤ))) :
    (tailGlue a h cc z₀ dep σ t).1 j =
      ugermC a h (((eqLam a : ℝ) : ℂ) ^ (-j) * (cc / (z₀ + t ^ (2 ^ (2 * dep))))) := by
  simp only [tailGlue]
  rw [dif_neg (by omega : ¬ ((dep : ℤ) ≤ j)),
    dif_neg (by omega : ¬ (-((dep : ℤ)) ≤ j))]

/-- The middle segment of the glued family: the F3 branch family. -/
theorem tailGlue_mid {a : ℝ} {h : ℂ → ℂ} {cc z₀ : ℂ} {dep : ℕ} {σ : Fin (2 * dep) → Bool}
    {t : ℂ} {j : ℤ} (hj1 : ¬ ((dep : ℤ) ≤ j)) (hj2 : -((dep : ℤ)) ≤ j) :
    (tailGlue a h cc z₀ dep σ t).1 j =
      branchPt a (endFun a h dep) z₀ 1 σ t
        ⟨(j + (dep : ℤ)).toNat, by
          have hpos : (0 : ℤ) ≤ j + (dep : ℤ) := by omega
          rw [Int.toNat_lt hpos]
          have hlt : j + (dep : ℤ) < ((2 * dep + 1 : ℕ) : ℤ) := by
            have h1' := hj1
            push_cast at h1' ⊢
            omega
          exact hlt⟩ := by
  simp only [tailGlue]
  rw [dif_neg hj1, dif_pos hj2]

end

end Work.EQ

namespace Work.EQ

open Complex Filter _root_.Topology

noncomputable section

/-- **The junction identity of the glued family at radius `ρ`.**

The first entry of the middle segment of `tailGlue a h c z₀ dep σ t` is the value of the unstable
leaf at depth `dep`.  When this holds, the glued datum is a chain (`Work.EQ.Chart.isChain_tailGlue`)
and the family `t ↦ tailGlue a h c z₀ dep σ t` is a family of chains of `⁰H`, hence the basis of a
punctured chart (Rychlik Thm 8(2)).  The radius `ρ` is a parameter because the tail identities are
only valid while `λ^dep ‖ψ₁‖`, `λ^dep ‖ψ₂‖ < ρg`. -/
def Junction (a : ℝ) (h : ℂ → ℂ) (c z₀ : ℂ) (dep : ℕ) (σ : Fin (2 * dep) → Bool)
    (ρ : ℝ) : Prop :=
  ∀ t : ℂ, 0 < ‖t‖ → ‖t‖ < ρ →
    branchPt a (endFun a h dep) z₀ 1 σ t ⟨0, by omega⟩ =
      ugermC a h (((eqLam a : ℝ) : ℂ) ^ dep * (c / (z₀ + t ^ (2 ^ (2 * dep)))))


/-- **A usable depth.**  There is a depth `dep ≥ max N 1` at which the germ is small throughout
the annulus: `λ^dep (r₂ + 1) < ρg` and `λ^dep (2 ‖c‖ / r₁) < ρg`. -/
theorem exists_depth {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {r₁ r₂ : ℝ} (hr₁ : 0 < r₁)
    (hr₂ : r₁ < r₂) {N : ℕ} {c : ℂ} {ρg : ℝ} (hρg : 0 < ρg) :
    ∃ dep : ℕ, N ≤ dep ∧ 1 ≤ dep ∧ (eqLam a) ^ dep * (r₂ + 1) < ρg ∧
      (eqLam a) ^ dep * (2 * ‖c‖ / r₁) < ρg := by
  have hlam0 : 0 < eqLam a := by rw [eqLam]; positivity
  have hlam1 : eqLam a < 1 := by rw [eqLam, div_lt_one (by linarith)]; linarith
  obtain ⟨n₁, hn₁⟩ := exists_pow_lt_of_lt_one (div_pos hρg (show (0:ℝ) < r₂ + 1 by linarith)) hlam1
  obtain ⟨n₂, hn₂⟩ := exists_pow_lt_of_lt_one (div_pos hρg (show (0:ℝ) < 2 * ‖c‖ / r₁ + 1 by positivity)) hlam1
  refine ⟨max N (max n₁ (max n₂ 1)), le_max_left _ _, ?_, ?_, ?_⟩
  · exact le_trans (le_max_right n₂ 1) (le_trans (le_max_right n₁ (max n₂ 1)) (le_max_right N (max n₁ (max n₂ 1))))
  · have h1 : (eqLam a) ^ (max N (max n₁ (max n₂ 1))) ≤ (eqLam a) ^ n₁ :=
      pow_le_pow_of_le_one hlam0.le hlam1.le (le_trans (le_max_left n₁ (max n₂ 1)) (le_max_right N (max n₁ (max n₂ 1))))
    calc (eqLam a) ^ (max N (max n₁ (max n₂ 1))) * (r₂ + 1)
        ≤ (eqLam a) ^ n₁ * (r₂ + 1) := mul_le_mul_of_nonneg_right h1 (by linarith)
      _ < (ρg / (r₂ + 1)) * (r₂ + 1) := mul_lt_mul_of_pos_right hn₁ (by linarith)
      _ = ρg := div_mul_cancel₀ ρg (by linarith : r₂ + 1 ≠ 0)
  · have h1 : (eqLam a) ^ (max N (max n₁ (max n₂ 1))) ≤ (eqLam a) ^ n₂ :=
      pow_le_pow_of_le_one hlam0.le hlam1.le (le_trans (le_max_left n₂ 1) (le_trans (le_max_right n₁ (max n₂ 1)) (le_max_right N (max n₁ (max n₂ 1)))))
    calc (eqLam a) ^ (max N (max n₁ (max n₂ 1))) * (2 * ‖c‖ / r₁)
        ≤ (eqLam a) ^ n₂ * (2 * ‖c‖ / r₁) := mul_le_mul_of_nonneg_right h1 (by positivity)
      _ ≤ (eqLam a) ^ n₂ * (2 * ‖c‖ / r₁ + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ < (ρg / (2 * ‖c‖ / r₁ + 1)) * (2 * ‖c‖ / r₁ + 1) :=
          mul_lt_mul_of_pos_right hn₂ (by positivity)
      _ = ρg := div_mul_cancel₀ ρg (by positivity : 2 * ‖c‖ / r₁ + 1 ≠ 0)

end

end Work.EQ
