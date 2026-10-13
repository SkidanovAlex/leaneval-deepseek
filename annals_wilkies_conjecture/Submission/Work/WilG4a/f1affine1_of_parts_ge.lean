/-
  WilG4a — the assembly of the **corrected** (`β ≥ 0`) affine family lemma `F1AffineGe`.

  ## Why this file exists

  The frozen `F1Affine1` (and its `Hχ`) demands `0 < β l` at *every* `l ∈ Λ`.  As the project lead
  established, that is **false**: for a family whose kinks sweep across `I` as `l` varies (e.g.
  `F i l x = 1/4 + |x − c_i(l)|/8` with the `4m+2` kinks `c_i(l) = j/m ± l`), the smooth component
  containing a given point has length `≤ 1/m` and moves at speed `1`, so no `β > 0`-everywhere
  chart can be valid at every `l`.  The paper's own proof uses *constant* charts (`β = 0`) for the
  degenerate cells (see `Work.WilG4a.chart1`'s junk value `1/2`), which the frozen statement
  forbids.

  The corrected statement (`F1AffineGe` below) keeps `β ≥ 0`, keeps the image inside `(0,1)`, and
  demands in the `ε`-cover that the covering charts have `β > 0`.  With that relaxation the
  assembly goes through verbatim, and the false global-chart input `Hχ` is replaced by the
  *trivial* chart `(α, β) = (1/2, 0)` (`Work.WilG4a.trivial_global_chart_ge`), whose composite is
  constant.

  Everything here is proved from the existing, sorry-free parts:

  * `Hχ`      ← `Work.WilG4a.trivial_global_chart_ge` (the trivial constant chart);
  * `HC`      ← `Work.WilG4a.cell_charts_with_fallback_ge` (the `β ≥ 0` variant);
  * `Hacc`    ← `Work.WilG4a.near_nondegen_fibre_at`;
  * `Hsh`     ← `Work.WilG4a.eval_add_const_bound`;
  * plus the bookkeeping `Work.WilG4a.poly_mul_pos_bound`, `cellDecomp_exists`,
    `sInf_sSup_fibre_graph_mem`, `affine_cover_params`, `ite_graph_mem`.
-/
import Mathlib
import Submission.Work.WilG4a.Defs
import Submission.Work.WilG4a.Cells
import Submission.Work.WilG4a.f1affine1_defs
import Submission.Work.WilG4a.cellDecomp_exists
import Submission.Work.WilG4a.goodCell_affine_charts
import Submission.Work.WilG4a.affine_cover_params
import Submission.Work.WilG4a.sInf_sSup_fibre_graph_mem
import Submission.Work.WilG4a.ite_graph_mem
import Submission.Work.WilG4a.Bounds
import Submission.Work.WilG4a.count_poly_comp
import Submission.Work.WilG4a.f1affine1_of_signConst
import Submission.Work.WilG4a.cell_charts_with_fallback_ge
import Submission.Work.WilG4a.trivial_fallback

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Classical
namespace Work.WilG4a

open WilkiesConjecture WilkiesDesign

/-- The per-chart conditions of the *corrected* `n = 1` family lemma: exactly `Chart1` with
`0 < β l` relaxed to `0 ≤ β l`.  This is what `Work.WilG4a.cell_charts_with_fallback_ge` and
`Work.WilG4a.trivial_global_chart_ge` produce. -/
def Chart1Ge (S : SOMin) (p : ℕ) (a bD : ℕ) (Λ : Set (Fin p → ℝ)) (k r : ℕ)
    (F : Fin k → (Fin p → ℝ) → ℝ → ℝ) (α β : (Fin p → ℝ) → ℝ) : Prop :=
  WilkiesDesign.graphOf α ∈ S.Ω a bD (p + 1) ∧
  WilkiesDesign.graphOf β ∈ S.Ω a bD (p + 1) ∧
  ∀ l ∈ Λ, 0 ≤ β l ∧ 0 ≤ α l ∧ α l + β l ≤ 1 ∧
    ∀ i, ContDiffOn ℝ r (fun t : ℝ => F i l (α l + β l * t)) I ∧
      ∀ m ≤ r, ∀ t ∈ I, |iteratedDeriv m (fun t : ℝ => F i l (α l + β l * t)) t| ≤ 1

/-- **BNZ Corollary 5.5 (`n = 1`), corrected**: affine charts `x = α l + β l · t` with `β ≥ 0`,
`Ω`-definable coefficients, an `ε`-cover of the *domain* `I` by charts with `β > 0`, and `C^r`
bounds along every chart for every family member at every `l ∈ Λ`. -/
def F1AffineGe (S : SOMin) (p : ℕ) : Prop :=
  ∀ F0 : ℕ, ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ) (c : MvPolynomial (Fin 4) ℝ),
    ∀ (D r k : ℕ) (ε : ℝ), 0 < ε → ε < 1 →
    ∀ (Λ : Set (Fin p → ℝ)) (F : Fin k → (Fin p → ℝ) → ℝ → ℝ),
      (∀ i, Work.WilG4a.graphFam (F i) ∈ S.Ω F0 D (p + 1 + 1)) →
      (∀ i, ∀ l ∈ Λ, ∀ x ∈ Work.WilG4a.I, F i l x ∈ Work.WilG4a.I) →
      ∃ Φ : Finset (((Fin p → ℝ) → ℝ) × ((Fin p → ℝ) → ℝ)),
        (Φ.card : ℝ) ≤ MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] c ∧
        (∀ αβ ∈ Φ, Chart1Ge S p a (MvPolynomial.eval ![D, r] b) Λ k r F αβ.1 αβ.2) ∧
        (∀ l ∈ Λ, ∀ x ∈ Work.WilG4a.I, ∃ αβ ∈ Φ, 0 < αβ.2 l ∧ ∃ t ∈ Work.WilG4a.I,
          |αβ.1 l + αβ.2 l * t - x| < ε)

/-- **The assembly, corrected.**  `F1AffineGe S p` follows from a (`β ≥ 0`) global chart, the
(`β ≥ 0`) per-cell chart package, the accumulation statement and the log-shift bookkeeping. -/
theorem f1affine1_of_parts_ge (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv)
    (hG3a : ∀ (r : ℕ) (f : ℝ → ℝ), ContDiffOn ℝ (r + 1) f (Set.Ioo 0 1) → (∀ x ∈ Set.Ioo (0 : ℝ) 1, f x ∈ Set.Ioo (0 : ℝ) 1) → (∀ j ≤ r + 1, (∀ x ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ iteratedDerivWithin j f (Set.Ioo 0 1) x) ∨ (∀ x ∈ Set.Ioo (0 : ℝ) 1, iteratedDerivWithin j f (Set.Ioo 0 1) x ≤ 0)) → ∀ M : ℝ, 1 < M → ∀ j ≤ r, ∀ x ∈ Set.Ioo (0 : ℝ) 1, (j : ℝ) / M < x → x < 1 - j / M → |iteratedDerivWithin j f (Set.Ioo 0 1) x| < M ^ j)
    (hG3b : ∀ (r : ℕ) (ε : ℝ), 0 < ε → ε < 1 → ∃ s : Finset (ℝ × ℝ), (s.card : ℝ) ≤ 8 * (r + 1) * (-Real.log ε + 2) ∧ (∀ p ∈ s, 0 < p.1 ∧ p.1 < p.2 ∧ p.2 < 1 ∧ (p.2 - p.1) * (r + 1) ≤ min p.1 (1 - p.2)) ∧ (Set.Icc ε (1 - ε) ⊆ (⋃ p ∈ s, Set.Icc p.1 p.2)))
    (p : ℕ)
    (Hχ : ∀ (F0 : ℕ), ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ),
      ∀ (D r k : ℕ) (Λ : Set (Fin p → ℝ)) (F : Fin k → (Fin p → ℝ) → ℝ → ℝ),
        (∀ i, Work.WilG4a.graphFam (F i) ∈ S.Ω F0 D (p + 1 + 1)) →
        (∀ i, ∀ l ∈ Λ, ∀ x ∈ Work.WilG4a.I, F i l x ∈ Work.WilG4a.I) →
        ∃ (α β : (Fin p → ℝ) → ℝ),
          Chart1Ge S p a (MvPolynomial.eval ![D, r] b) Λ k r F α β)
    (HC : ∀ (F0 Fκ : ℕ) (bκ : MvPolynomial (Fin 2) ℕ),
      ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ) (c : MvPolynomial (Fin 4) ℝ),
      ∀ (D r k : ℕ) (ε : ℝ), 0 < ε → ε < 1 →
      ∀ (Λ : Set (Fin p → ℝ)) (F : Fin k → (Fin p → ℝ) → ℝ → ℝ)
        (κ : Set (Fin (p + 1) → ℝ)) (α₀ β₀ : (Fin p → ℝ) → ℝ),
        (∀ i, Work.WilG4a.graphFam (F i) ∈ S.Ω F0 D (p + 1 + 1)) →
        (∀ i, ∀ l ∈ Λ, ∀ x ∈ Work.WilG4a.I, F i l x ∈ Work.WilG4a.I) →
        Work.WilG4a.GoodCell_w k r F κ →
        κ ∈ S.Ω Fκ (MvPolynomial.eval ![D, r] bκ) (p + 1) →
        WilkiesDesign.graphOf α₀ ∈ S.Ω Fκ (MvPolynomial.eval ![D, r] bκ) (p + 1) →
        WilkiesDesign.graphOf β₀ ∈ S.Ω Fκ (MvPolynomial.eval ![D, r] bκ) (p + 1) →
        (∀ l ∈ Λ, 0 ≤ β₀ l ∧ 0 ≤ α₀ l ∧ α₀ l + β₀ l ≤ 1 ∧
          ∀ i, ContDiffOn ℝ r (fun t : ℝ => F i l (α₀ l + β₀ l * t)) Work.WilG4a.I ∧
            ∀ m ≤ r, ∀ t ∈ Work.WilG4a.I,
              |iteratedDeriv m (fun t : ℝ => F i l (α₀ l + β₀ l * t)) t| ≤ 1) →
        ∃ Φ : Finset (((Fin p → ℝ) → ℝ) × ((Fin p → ℝ) → ℝ)),
          (Φ.card : ℝ) ≤ MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] c ∧
          (∀ αβ ∈ Φ, Chart1Ge S p a (MvPolynomial.eval ![D, r] b) Λ k r F αβ.1 αβ.2) ∧
          (∀ l ∈ Λ, ¬ (Work.WilG4a.fibre κ l).Subsingleton → ∀ x ∈ Work.WilG4a.fibre κ l,
            ∃ αβ ∈ Φ, 0 < αβ.2 l ∧ ∃ t ∈ Work.WilG4a.I,
              |αβ.1 l + αβ.2 l * t - x| < ε))
    (Hacc : ∀ (m : ℕ) (κ : Fin m → Set (Fin (p + 1) → ℝ)) (l : Fin p → ℝ)
      (x : ℝ) (ε : ℝ),
        0 < ε →
        (∀ y ∈ Work.WilG4a.I, ∃ σ, Fin.snoc l y ∈ κ σ) →
        (∀ (σ : Fin m), (Work.WilG4a.fibre (κ σ) l).Subsingleton ∨
          ∃ a b : ℝ, a < b ∧ Work.WilG4a.fibre (κ σ) l = Set.Ioo a b) →
        x ∈ Work.WilG4a.I →
        ∃ σ, ∃ y ∈ Work.WilG4a.fibre (κ σ) l,
          |y - x| < ε ∧ ¬ (Work.WilG4a.fibre (κ σ) l).Subsingleton)
    (Hsh : ∀ (p : MvPolynomial (Fin 4) ℝ) (c : ℝ), 0 ≤ c →
      ∃ p' : MvPolynomial (Fin 4) ℝ, ∀ (D r k : ℕ) (L : ℝ), 0 ≤ L →
        p.eval ![(D : ℝ), (r : ℝ), (k : ℝ), L + c] ≤
          p'.eval ![(D : ℝ), (r : ℝ), (k : ℝ), L])
    : Work.WilG4a.F1AffineGe S p := by
  intro F0
  obtain ⟨aC, bC, ccC, hC⟩ := cellDecomp_exists S hcd hder p F0
  obtain ⟨aE, cE, dE, hE⟩ := sInf_sSup_fibre_graph_mem S p (max aC (p + 4))
  obtain ⟨aP, bP, hP⟩ := Hχ F0
  -- a common format/degree for the cells, their endpoint functions and the global chart
  set Fκ : ℕ := max (max aC (p + 4)) (max aE aP) + 1 with hFκ
  set bκ : MvPolynomial (Fin 2) ℕ := bC + MvPolynomial.C cE * bC + MvPolynomial.C dE + bP + 1
    with hbκ
  obtain ⟨aA, bA, cA, hA⟩ := HC F0 Fκ bκ
  -- the log-shift of the per-cell count bound (`-log (ε/2) = -log ε + log 2`) and the
  -- product bookkeeping
  obtain ⟨cA', hcA'⟩ := Hsh cA (Real.log 2) (Real.log_nonneg one_le_two)
  obtain ⟨ccF, hccF⟩ := poly_mul_pos_bound ccC cA'
  refine ⟨aA, bA, ccF, ?_⟩
  intro D r k ε hε hε1 Λ F hFΩ hFI
  have hlog : (0 : ℝ) ≤ -Real.log ε := by
    rw [neg_nonneg]; exact Real.log_nonpos (le_of_lt hε) (le_of_lt hε1)
  obtain ⟨m, hmcard, κ, hκΩ, hκdich, hκcov⟩ := hC D r k Λ F hFΩ hFI
  obtain ⟨α₀, β₀, hφ₀⟩ := hP D r k Λ F hFΩ hFI
  obtain ⟨hα₀, hβ₀, hφ₀pt⟩ := hφ₀
  -- degree/format bookkeeping: everything is raised to `(Fκ, bκ)`
  have hbC_le : MvPolynomial.eval ![D, r] bC ≤ MvPolynomial.eval ![D, r] bκ := by
    rw [hbκ, MvPolynomial.eval_add, MvPolynomial.eval_add, MvPolynomial.eval_add,
      MvPolynomial.eval_add]
    simp only [MvPolynomial.eval_mul, MvPolynomial.eval_C]
    ring_nf
    omega
  have hP_le : MvPolynomial.eval ![D, r] bP ≤ MvPolynomial.eval ![D, r] bκ := by
    rw [hbκ, MvPolynomial.eval_add, MvPolynomial.eval_add, MvPolynomial.eval_add,
      MvPolynomial.eval_add]
    simp only [MvPolynomial.eval_mul, MvPolynomial.eval_C]
    ring_nf
    omega
  have hκΩ' : ∀ σ, κ σ ∈ S.Ω Fκ (MvPolynomial.eval ![D, r] bκ) (p + 1) :=
    fun σ => mono_FD_le S (hκΩ σ) (by simp only [hFκ]; omega) hbC_le
  have hα₀' : WilkiesDesign.graphOf α₀ ∈ S.Ω Fκ (MvPolynomial.eval ![D, r] bκ) (p + 1) :=
    mono_FD_le S hα₀ (by simp only [hFκ]; omega) hP_le
  have hβ₀' : WilkiesDesign.graphOf β₀ ∈ S.Ω Fκ (MvPolynomial.eval ![D, r] bκ) (p + 1) :=
    mono_FD_le S hβ₀ (by simp only [hFκ]; omega) hP_le
  -- The per-cell chart families: for a good cell, the cell's own charts glued with the global
  -- chart `φ₀` (`HC`), for a degenerate cell the empty family.  Then `Φ := ⋃_σ Φ_σ`.
  have hex : ∀ σ : Fin m, ∃ Φσ : Finset (((Fin p → ℝ) → ℝ) × ((Fin p → ℝ) → ℝ)),
      ((Φσ.card : ℝ) ≤
        max 0 (MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] cA')) ∧
      (∀ αβ ∈ Φσ, Chart1Ge S p aA (MvPolynomial.eval ![D, r] bA) Λ k r F αβ.1 αβ.2) ∧
      (∀ l ∈ Λ, ¬ (Work.WilG4a.fibre (κ σ) l).Subsingleton →
        ∀ x ∈ Work.WilG4a.fibre (κ σ) l,
          ∃ αβ ∈ Φσ, 0 < αβ.2 l ∧ ∃ t ∈ Work.WilG4a.I,
            |αβ.1 l + αβ.2 l * t - x| < ε / 2) := by
    intro σ
    rcases hκdich σ with hg | hd
    · obtain ⟨Φσ, hcard, hfam, hcov⟩ := hA D r k (ε / 2) (by linarith) (by linarith) Λ F
        (κ σ) α₀ β₀ hFΩ hFI hg (hκΩ' σ) hα₀' hβ₀' hφ₀pt
      have heq : -Real.log (ε / 2) = -Real.log ε + Real.log 2 := by
        rw [Real.log_div (ne_of_gt hε) (by norm_num)]; ring
      rw [heq] at hcard
      exact ⟨Φσ, le_trans (le_trans hcard (hcA' D r k (-Real.log ε) hlog))
        (le_max_right 0 _), hfam, hcov⟩
    · exact ⟨∅, by simp,
        by intro αβ hαβ; exact absurd hαβ (Finset.notMem_empty αβ),
        by intro l _ hsub; exact absurd (hd l) hsub⟩
  choose Φσ hΦσ using hex
  refine ⟨Finset.univ.biUnion Φσ, ?_, ?_, ?_⟩
  · -- cardinality: `Finset.card_biUnion_le`, `m ≤ ccC.eval`, `|Φ_σ| ≤ cA'.eval`,
    -- `poly_mul_pos_bound`
    have h1 : ((Finset.univ.biUnion Φσ).card : ℝ) ≤ ∑ σ : Fin m, ((Φσ σ).card : ℝ) := by
      exact_mod_cast Finset.card_biUnion_le (s := Finset.univ) (t := Φσ)
    have h2 : (∑ σ : Fin m, ((Φσ σ).card : ℝ)) ≤
        ∑ _σ : Fin m,
          max 0 (MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] cA') :=
      Finset.sum_le_sum (fun σ _ => (hΦσ σ).1)
    have h3 : (∑ _σ : Fin m,
          max 0 (MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] cA')) =
        (m : ℝ) * max 0 (MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] cA') := by
      rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    have h4 : (m : ℝ) *
          max 0 (MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] cA') ≤
        ccC.eval ![(D : ℝ), (r : ℝ), (k : ℝ)] *
          max 0 (MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] cA') :=
      mul_le_mul_of_nonneg_right hmcard (le_max_left 0 _)
    exact le_trans h1 (le_trans h2 (le_trans (le_of_eq h3) (le_trans h4
      (hccF D r k (-Real.log ε) hlog))))
  · -- the per-chart conditions
    exact fun αβ hαβ => by
      rw [Finset.mem_biUnion] at hαβ
      obtain ⟨σ, -, hσ⟩ := hαβ
      exact (hΦσ σ).2.1 αβ hσ
  · -- the ε-cover
    intro l hl x hx
    obtain ⟨σ, hσ⟩ := hκcov l hl x hx
    have hsub : ∀ τ : Fin m, (Work.WilG4a.fibre (κ τ) l).Subsingleton ∨
        ∃ a b : ℝ, a < b ∧ Work.WilG4a.fibre (κ τ) l = Set.Ioo a b := by
      intro τ
      rcases hκdich τ with hg | hd
      · rcases hg.2.1 l with h1 | ⟨a, b, hfib⟩
        · exact Or.inl h1
        · rcases Set.eq_empty_or_nonempty (Work.WilG4a.fibre (κ τ) l) with he | ⟨y, hy⟩
          · exact Or.inl (he ▸ Set.subsingleton_empty)
          · have hy' : y ∈ Set.Ioo a b := hfib ▸ hy
            exact Or.inr ⟨a, b, hy'.1.trans hy'.2, hfib⟩
      · exact Or.inl (hd l)
    by_cases hnd : (Work.WilG4a.fibre (κ σ) l).Subsingleton
    · -- degenerate fibre: `Hacc` gives a nearby nondegenerate fibre, whose chart covers `y`,
      -- and `|· - x| ≤ |· - y| + |y - x| < ε/2 + ε/2`
      obtain ⟨τ, y, hy, hlt, hndτ⟩ :=
        Hacc m κ l x (ε / 2) (by linarith) (fun y' hy' => hκcov l hl y' hy') hsub hx
      obtain ⟨αβ, hαβ, hβpos, t, ht, hcov⟩ := (hΦσ τ).2.2 l hl hndτ y hy
      refine ⟨αβ, Finset.mem_biUnion.mpr ⟨τ, Finset.mem_univ τ, hαβ⟩, hβpos, t, ht, ?_⟩
      have htri : |αβ.1 l + αβ.2 l * t - x| ≤
          |αβ.1 l + αβ.2 l * t - y| + |y - x| := by
        have h := abs_add_le (αβ.1 l + αβ.2 l * t - y) (y - x)
        rwa [show αβ.1 l + αβ.2 l * t - y + (y - x) = αβ.1 l + αβ.2 l * t - x by ring] at h
      linarith
    · -- nondegenerate fibre: the cell's own charts cover `x` up to `ε/2 < ε`
      obtain ⟨αβ, hαβ, hβpos, t, ht, hcov⟩ := (hΦσ σ).2.2 l hl hnd x hσ
      exact ⟨αβ, Finset.mem_biUnion.mpr ⟨σ, Finset.mem_univ σ, hαβ⟩, hβpos, t, ht,
        lt_of_lt_of_le hcov (by linarith)⟩

/-- **The corrected target, in every parameter dimension.**  This is `f1affine1_all` with `0 < β`
relaxed to `0 ≤ β` (and `β > 0` required in the `ε`-cover).  It is proved from
`signConst_decomposition`-type parts only through the four inputs, each of which is now available:
`Work.WilG4a.trivial_global_chart_ge` (`Hχ`), `Work.WilG4a.cell_charts_with_fallback_ge` (`HC`),
`Work.WilG4a.near_nondegen_fibre_at` (`Hacc`) and `Work.WilG4a.eval_add_const_bound` (`Hsh`). -/
theorem f1affine1_ge_all (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv)
    (hL1 : ∀ (p F0 : ℕ), ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ) (cc : MvPolynomial (Fin 3) ℝ), ∀ (D r k : ℕ) (F : Fin k → (Fin p → ℝ) → ℝ → ℝ), (∀ i, Work.WilG4a.graphFam (F i) ∈ S.Ω F0 D (p + 1 + 1)) → ∃ (m : ℕ), (m : ℝ) ≤ MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ)] cc ∧ ∃ (κ : Fin m → Set (Fin (p + 1) → ℝ)), (∀ σ, κ σ ∈ S.Ω a (MvPolynomial.eval ![D, r] b) (p + 1)) ∧ (∀ z : Fin (p + 1) → ℝ, ∃ σ, z ∈ κ σ) ∧ (∀ σ σ' : Fin m, σ ≠ σ' → Disjoint (κ σ) (κ σ')) ∧ (∀ σ (l : Fin p → ℝ), (∃ x : ℝ, Fin.snoc l x ∈ κ σ) → (∃ x : ℝ, Work.WilG4a.fibre (κ σ) l = {x}) ∨ (∃ a b : EReal, Work.WilG4a.fibre (κ σ) l = {y : ℝ | a < (y : EReal) ∧ (y : EReal) < b})) ∧ (∀ (σ : Fin m) (i : Fin k) (j : ℕ), j ≤ r + 2 → Disjoint (κ σ) (Work.WilG4a.badLocus (F i) j) ∨ κ σ ⊆ Work.WilG4a.badLocus (F i) j) ∧ (∀ (σ : Fin m) (i : Fin k) (j : ℕ), j ≤ r + 2 → Disjoint (κ σ) (Work.WilG4a.derivZeroSet (F i) j) ∨ κ σ ⊆ Work.WilG4a.derivZeroSet (F i) j) ∧ (∀ (σ : Fin m) (i : Fin k) (j : ℕ), j ≤ r + 1 → ∀ (l : Fin p → ℝ) (u v : ℝ), u < v → Set.Ioo u v ⊆ Work.WilG4a.fibre (κ σ) l → Disjoint (κ σ) (Work.WilG4a.badLocus (F i) (r + 2)) → (Disjoint (κ σ) (Work.WilG4a.derivZeroSet (F i) j) ∨ κ σ ⊆ Work.WilG4a.derivZeroSet (F i) j) → (∀ x ∈ Set.Ioo u v, ContDiffAt ℝ (r + 2) (fun y : ℝ => F i l y) x) ∧ ((∀ x ∈ Set.Ioo u v, 0 ≤ iteratedDeriv j (fun y : ℝ => F i l y) x) ∨ (∀ x ∈ Set.Ioo u v, iteratedDeriv j (fun y : ℝ => F i l y) x ≤ 0))))
    (hG3a : ∀ (r : ℕ) (f : ℝ → ℝ), ContDiffOn ℝ (r + 1) f (Set.Ioo 0 1) → (∀ x ∈ Set.Ioo (0 : ℝ) 1, f x ∈ Set.Ioo (0 : ℝ) 1) → (∀ j ≤ r + 1, (∀ x ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ iteratedDerivWithin j f (Set.Ioo 0 1) x) ∨ (∀ x ∈ Set.Ioo (0 : ℝ) 1, iteratedDerivWithin j f (Set.Ioo 0 1) x ≤ 0)) → ∀ M : ℝ, 1 < M → ∀ j ≤ r, ∀ x ∈ Set.Ioo (0 : ℝ) 1, (j : ℝ) / M < x → x < 1 - j / M → |iteratedDerivWithin j f (Set.Ioo 0 1) x| < M ^ j)
    (hG3b : ∀ (r : ℕ) (ε : ℝ), 0 < ε → ε < 1 → ∃ s : Finset (ℝ × ℝ), (s.card : ℝ) ≤ 8 * (r + 1) * (-Real.log ε + 2) ∧ (∀ p ∈ s, 0 < p.1 ∧ p.1 < p.2 ∧ p.2 < 1 ∧ (p.2 - p.1) * (r + 1) ≤ min p.1 (1 - p.2)) ∧ (Set.Icc ε (1 - ε) ⊆ (⋃ p ∈ s, Set.Icc p.1 p.2))) :
    ∀ p : ℕ, Work.WilG4a.F1AffineGe S p :=
  fun p => f1affine1_of_parts_ge S hcd hder hG3a hG3b p (trivial_global_chart_ge S p)
    (fun F0 Fκ bκ => cell_charts_with_fallback_ge S hG3a hG3b p F0 Fκ bκ)
    (fun m κ l x ε hε hcov hsub hx => near_nondegen_fibre_at κ l x ε hε hcov hsub hx)
    (fun q c _ => eval_add_const_bound q c)

end Work.WilG4a
