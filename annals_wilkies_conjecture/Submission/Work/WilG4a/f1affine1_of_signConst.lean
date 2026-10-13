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
import Submission.Work.WilG4a.exists_near_nondegen_fibre
import Submission.Work.WilG1.Basic

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Classical
namespace Work.WilG4a
open WilkiesConjecture WilkiesDesign

/-! ## Vocabulary: the per-chart conditions

`Chart1` collects the conditions on a single affine chart `x = α l + β l t` demanded by
`F1Affine1` (its graphs are `Ω`-definable at format `a` and degree `bD`, and the chart is
*valid at every* `l ∈ Λ`), and `ChartFam` is the same condition for a finite family of charts.
These are introduced as named constants so that the (very large) conjunction is not re-elaborated
at every step of the assembly. -/

/-- The conditions on a single affine chart `x = α l = β l * t`. -/
def Chart1 (S : SOMin) (p : ℕ) (a bD : ℕ) (Λ : Set (Fin p → ℝ)) (k r : ℕ)
    (F : Fin k → (Fin p → ℝ) → ℝ → ℝ) (α β : (Fin p → ℝ) → ℝ) : Prop :=
  WilkiesDesign.graphOf α ∈ S.Ω a bD (p + 1) ∧
  WilkiesDesign.graphOf β ∈ S.Ω a bD (p + 1) ∧
  ∀ l ∈ Λ, 0 < β l ∧ 0 ≤ α l ∧ α l + β l ≤ 1 ∧
    ∀ i, ContDiffOn ℝ r (fun t : ℝ => F i l (α l + β l * t)) I ∧
      ∀ m ≤ r, ∀ t ∈ I, |iteratedDeriv m (fun t : ℝ => F i l (α l + β l * t)) t| ≤ 1

/-- `ChartFam` is the per-chart condition of the conclusion of `F1Affine1`. -/
def ChartFam (S : SOMin) (p : ℕ) (a bD : ℕ) (Λ : Set (Fin p → ℝ)) (k r : ℕ)
    (F : Fin k → (Fin p → ℝ) → ℝ → ℝ)
    (Φ : Finset (((Fin p → ℝ) → ℝ) × ((Fin p → ℝ) → ℝ))) : Prop :=
  ∀ αβ ∈ Φ, Chart1 S p a bD Λ k r F αβ.1 αβ.2

theorem chartFam_iff (S : SOMin) (p a bD : ℕ) (Λ : Set (Fin p → ℝ)) (k r : ℕ)
    (F : Fin k → (Fin p → ℝ) → ℝ → ℝ)
    (Φ : Finset (((Fin p → ℝ) → ℝ) × ((Fin p → ℝ) → ℝ))) :
    ChartFam S p a bD Λ k r F Φ ↔
      ∀ αβ ∈ Φ,
        WilkiesDesign.graphOf αβ.1 ∈ S.Ω a bD (p + 1) ∧
        WilkiesDesign.graphOf αβ.2 ∈ S.Ω a bD (p + 1) ∧
        (∀ l ∈ Λ, 0 < αβ.2 l ∧ 0 ≤ αβ.1 l ∧ αβ.1 l + αβ.2 l ≤ 1 ∧
          ∀ i, ContDiffOn ℝ r (fun t : ℝ => F i l (αβ.1 l + αβ.2 l * t)) I ∧
            ∀ m ≤ r, ∀ t ∈ I,
              |iteratedDeriv m (fun t : ℝ => F i l (αβ.1 l + αβ.2 l * t)) t| ≤ 1) :=
  Iff.rfl

/-!
## The `n = 1` family lemma (BNZ Cor. 5.5) from its pieces

`F1Affine1 S p` demands, for every family `F` of `k` `Ω`-definable functions on `Λ × I` with
values in `I`, a finite collection `Φ` of affine charts `x = α l + β l · t` with

* `Ω`-definable graphs of format `a` and degree `poly(D,r)` (independent of `k`, `ε`),
* validity at *every* `l ∈ Λ`: `0 < β l`, `0 ≤ α l`, `α l + β l ≤ 1` and the `C^r` bounds on
  the composites `t ↦ F i l (α l + β l t)`,
* an `ε`-cover of `I` at every `l ∈ Λ`.

The proof splits the strip into cells (`cellDecomp_exists`), takes the per-cell affine charts
(valid on the *nondegeneracy locus* of the cell, `goodCell_affine_charts`), glues each of them
with a *globally valid* chart `φ₀` by a case split (`ite_graph_mem`) so that every chart of
`Φ` is valid on all of `Λ`, and finally `ε`-covers the points lying in degenerate fibres by the
neighbouring nondegenerate fibres (`exists_near_nondegen_fibre`).
-/

/-- Product bookkeeping: given two `ℝ`-polynomials in the variables `(D,r,k)` resp.
`(D,r,k,ε)`, there is one polynomial `c` in `(D,r,k,ε)` with

`p₃.eval (D,r,k) * max 0 (p₄.eval (D,r,k,ε)) ≤ c.eval (D,r,k,ε)`

for all `D r k : ℕ` and `ε ≥ 0`.  (The count bound `m ≤ p₃.eval` of the cell decomposition
and the per-cell count bound `|Φ_σ| ≤ p₄.eval` are multiplied this way.) -/
theorem poly_mul_pos_bound (p3 : MvPolynomial (Fin 3) ℝ) (p4 : MvPolynomial (Fin 4) ℝ) :
    ∃ c : MvPolynomial (Fin 4) ℝ, ∀ D r k : ℕ, ∀ L : ℝ, 0 ≤ L →
      p3.eval ![(D : ℝ), (r : ℝ), (k : ℝ)] * max 0 (p4.eval ![(D : ℝ), (r : ℝ), (k : ℝ), L]) ≤
        c.eval ![(D : ℝ), (r : ℝ), (k : ℝ), L] := by
  refine ⟨MvPolynomial.rename (Fin.castSucc : Fin 3 → Fin 4) (p3 * p3) + p4 * p4, ?_⟩
  intro D r k L _
  have hpt : (![(D : ℝ), (r : ℝ), (k : ℝ), L] ∘ (Fin.castSucc : Fin 3 → Fin 4))
      = ![(D : ℝ), (r : ℝ), (k : ℝ)] := by
    funext i; fin_cases i <;> rfl
  have hren : MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), L]
        (MvPolynomial.rename (Fin.castSucc : Fin 3 → Fin 4) (p3 * p3))
      = (MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ)] p3) ^ 2 := by
    rw [MvPolynomial.eval_rename, hpt, MvPolynomial.eval_mul]; ring
  rw [MvPolynomial.eval_add, hren, MvPolynomial.eval_mul]
  set a := MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ)] p3
  set b := MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), L] p4
  by_cases hb : 0 ≤ b
  · rw [max_eq_right hb]
    nlinarith [sq_nonneg (a - b), sq_nonneg a, sq_nonneg b]
  · rw [max_eq_left (le_of_lt (not_le.mp hb))]
    nlinarith [sq_nonneg a, sq_nonneg b]

/-- Polynomial bookkeeping: an upper bound at `L + c` (`c` an arbitrary constant) converts
into an upper bound at `L`.  (Used with `c = Real.log 2`, since `-log (ε/2) = -log ε + log 2`.) -/
theorem eval_add_const_bound (p : MvPolynomial (Fin 4) ℝ) (c : ℝ) :
    ∃ p' : MvPolynomial (Fin 4) ℝ, ∀ (D r k : ℕ) (L : ℝ), 0 ≤ L →
      p.eval ![(D : ℝ), (r : ℝ), (k : ℝ), L + c] ≤
        p'.eval ![(D : ℝ), (r : ℝ), (k : ℝ), L] := by
  refine ⟨MvPolynomial.bind₁ (fun i : Fin 4 =>
    if i = 3 then MvPolynomial.X 3 + MvPolynomial.C c else MvPolynomial.X i) p, ?_⟩
  intro D r k L _
  have h := MvPolynomial.eval₂Hom_bind₁ (RingHom.id ℝ) ![(D : ℝ), (r : ℝ), (k : ℝ), L]
    (fun i : Fin 4 => if i = 3 then MvPolynomial.X 3 + MvPolynomial.C c
      else MvPolynomial.X i) p
  have hfun : (fun i : Fin 4 => MvPolynomial.eval₂Hom (RingHom.id ℝ)
      ![(D : ℝ), (r : ℝ), (k : ℝ), L]
      (if i = 3 then MvPolynomial.X 3 + MvPolynomial.C c else MvPolynomial.X i))
      = ![(D : ℝ), (r : ℝ), (k : ℝ), L + c] := by
    funext i; fin_cases i <;> simp
  rw [hfun] at h
  change MvPolynomial.eval₂Hom (RingHom.id ℝ) ![(D : ℝ), (r : ℝ), (k : ℝ), L + c] p ≤
    MvPolynomial.eval₂Hom (RingHom.id ℝ) ![(D : ℝ), (r : ℝ), (k : ℝ), L]
      (MvPolynomial.bind₁ (fun i : Fin 4 =>
        if i = 3 then MvPolynomial.X 3 + MvPolynomial.C c else MvPolynomial.X i) p)
  exact le_of_eq h.symm

/-- **The accumulation lemma** (the fixed-parameter form of `exists_near_nondegen_fibre`): if
the fibres over `l` of the finitely many sets `κ σ` cover `I`, then every `x ∈ I` is within `ε`
of a point of a fibre that is not a subsingleton.  (The `hsub` hypothesis is unused; it is
carried because the assembly supplies it.) -/
theorem near_nondegen_fibre_at {p m : ℕ} (κ : Fin m → Set (Fin (p + 1) → ℝ)) (l : Fin p → ℝ)
    (x : ℝ) (ε : ℝ) (hε : 0 < ε)
    (hcover : ∀ y ∈ Work.WilG4a.I, ∃ σ, Fin.snoc l y ∈ κ σ)
    (_hsub : ∀ (σ : Fin m), (Work.WilG4a.fibre (κ σ) l).Subsingleton ∨
      ∃ a b : ℝ, a < b ∧ Work.WilG4a.fibre (κ σ) l = Set.Ioo a b)
    (hx : x ∈ Work.WilG4a.I) :
    ∃ σ, ∃ y ∈ Work.WilG4a.fibre (κ σ) l,
      |y - x| < ε ∧ ¬ (Work.WilG4a.fibre (κ σ) l).Subsingleton := by
  obtain ⟨hx0, hx1⟩ := hx
  -- a small radius around `x` which still lies inside `I ∩ (x-ε, x+ε)`
  set δ : ℝ := min ε (min x (1 - x)) / 2 with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    linarith [lt_min hε (lt_min hx0 (by linarith : (0 : ℝ) < 1 - x))]
  have hδε : δ < ε := by
    have h := min_le_left ε (min x (1 - x)); rw [hδdef]; linarith
  have hδx : δ < x := by
    have h1 := min_le_right ε (min x (1 - x))
    have h2 := min_le_left x (1 - x); rw [hδdef]; linarith
  have hδ1 : δ < 1 - x := by
    have h1 := min_le_right ε (min x (1 - x))
    have h2 := min_le_right x (1 - x); rw [hδdef]; linarith
  have hsubIoo : Set.Ioo (x - δ) (x + δ) ⊆ Work.WilG4a.I ∩ Set.Ioo (x - ε) (x + ε) := by
    intro y hy
    obtain ⟨hy1, hy2⟩ := hy
    exact ⟨⟨by linarith, by linarith⟩, by linarith, by linarith⟩
  have hSinf : (Work.WilG4a.I ∩ Set.Ioo (x - ε) (x + ε)).Infinite :=
    Set.Infinite.mono hsubIoo (Set.Ioo_infinite (by linarith))
  have hcoverS : Work.WilG4a.I ∩ Set.Ioo (x - ε) (x + ε) ⊆
      ⋃ σ : Fin m, Work.WilG4a.fibre (κ σ) l := by
    intro y hy
    obtain ⟨σ, hσ⟩ := hcover y hy.1
    exact Set.mem_iUnion.mpr ⟨σ, hσ⟩
  -- some fibre meets `I ∩ (x-ε, x+ε)` in infinitely many points
  obtain ⟨σ, hσinf⟩ : ∃ σ : Fin m,
      (Work.WilG4a.fibre (κ σ) l ∩ (Work.WilG4a.I ∩ Set.Ioo (x - ε) (x + ε))).Infinite := by
    by_contra hcon
    have hfin : ∀ σ : Fin m,
        (Work.WilG4a.fibre (κ σ) l ∩ (Work.WilG4a.I ∩ Set.Ioo (x - ε) (x + ε))).Finite := by
      intro σ
      by_contra hf
      exact hcon ⟨σ, hf⟩
    have hunionfin : (⋃ σ : Fin m,
        Work.WilG4a.fibre (κ σ) l ∩ (Work.WilG4a.I ∩ Set.Ioo (x - ε) (x + ε))).Finite :=
      Set.finite_iUnion hfin
    have hsub' : Work.WilG4a.I ∩ Set.Ioo (x - ε) (x + ε) ⊆
        ⋃ σ : Fin m, Work.WilG4a.fibre (κ σ) l ∩
          (Work.WilG4a.I ∩ Set.Ioo (x - ε) (x + ε)) := by
      intro y hy
      obtain ⟨σ, hσ⟩ := Set.mem_iUnion.mp (hcoverS hy)
      exact Set.mem_iUnion.mpr ⟨σ, hσ, hy⟩
    exact hSinf (hunionfin.subset hsub')
  have hnondeg : ¬ (Work.WilG4a.fibre (κ σ) l).Subsingleton := by
    intro h
    exact hσinf (h.finite.inter_of_left _)
  obtain ⟨y, hy⟩ := hσinf.nonempty
  refine ⟨σ, y, hy.1, ?_, hnondeg⟩
  rw [abs_lt]
  exact ⟨by linarith [hy.2.2.1], by linarith [hy.2.2.2]⟩

/-- **The assembly.**  `F1Affine1 S p` follows from three ingredients: a globally valid chart
`φ₀` (used as the inactive branch of the case split), the per-cell chart package, and the
"accumulation" statement covering degenerate fibres by nondegenerate ones. -/
theorem f1affine1_of_parts (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv)
    (hG3a : ∀ (r : ℕ) (f : ℝ → ℝ), ContDiffOn ℝ (r + 1) f (Set.Ioo 0 1) → (∀ x ∈ Set.Ioo (0 : ℝ) 1, f x ∈ Set.Ioo (0 : ℝ) 1) → (∀ j ≤ r + 1, (∀ x ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ iteratedDerivWithin j f (Set.Ioo 0 1) x) ∨ (∀ x ∈ Set.Ioo (0 : ℝ) 1, iteratedDerivWithin j f (Set.Ioo 0 1) x ≤ 0)) → ∀ M : ℝ, 1 < M → ∀ j ≤ r, ∀ x ∈ Set.Ioo (0 : ℝ) 1, (j : ℝ) / M < x → x < 1 - j / M → |iteratedDerivWithin j f (Set.Ioo 0 1) x| < M ^ j)
    (hG3b : ∀ (r : ℕ) (ε : ℝ), 0 < ε → ε < 1 → ∃ s : Finset (ℝ × ℝ), (s.card : ℝ) ≤ 8 * (r + 1) * (-Real.log ε + 2) ∧ (∀ p ∈ s, 0 < p.1 ∧ p.1 < p.2 ∧ p.2 < 1 ∧ (p.2 - p.1) * (r + 1) ≤ min p.1 (1 - p.2)) ∧ (Set.Icc ε (1 - ε) ⊆ (⋃ p ∈ s, Set.Icc p.1 p.2)))
    (p : ℕ)
    (Hχ : ∀ (F0 : ℕ), ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ),
      ∀ (D r k : ℕ) (Λ : Set (Fin p → ℝ)) (F : Fin k → (Fin p → ℝ) → ℝ → ℝ),
        (∀ i, Work.WilG4a.graphFam (F i) ∈ S.Ω F0 D (p + 1 + 1)) →
        (∀ i, ∀ l ∈ Λ, ∀ x ∈ Work.WilG4a.I, F i l x ∈ Work.WilG4a.I) →
        ∃ (α β : (Fin p → ℝ) → ℝ),
          Chart1 S p a (MvPolynomial.eval ![D, r] b) Λ k r F α β)
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
        Chart1 S p Fκ (MvPolynomial.eval ![D, r] bκ) Λ k r F α₀ β₀ →
        ∃ Φ : Finset (((Fin p → ℝ) → ℝ) × ((Fin p → ℝ) → ℝ)),
          (Φ.card : ℝ) ≤ MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] c ∧
          ChartFam S p a (MvPolynomial.eval ![D, r] b) Λ k r F Φ ∧
          (∀ l ∈ Λ, ¬ (Work.WilG4a.fibre κ l).Subsingleton → ∀ x ∈ Work.WilG4a.fibre κ l,
            ∃ αβ ∈ Φ, ∃ t ∈ Work.WilG4a.I, |αβ.1 l + αβ.2 l * t - x| < ε))
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
    : Work.WilG4a.F1Affine1 S p := by
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
  obtain ⟨α₀, β₀, hα₀, hβ₀, hφ₀⟩ := hP D r k Λ F hFΩ hFI
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
  have hφ₀' : Chart1 S p Fκ (MvPolynomial.eval ![D, r] bκ) Λ k r F α₀ β₀ := by
    have h1 : WilkiesDesign.graphOf α₀ ∈ S.Ω Fκ (MvPolynomial.eval ![D, r] bκ) (p + 1) := hα₀'
    have h2 : WilkiesDesign.graphOf β₀ ∈ S.Ω Fκ (MvPolynomial.eval ![D, r] bκ) (p + 1) := hβ₀'
    have h3 : ∀ l ∈ Λ, 0 < β₀ l ∧ 0 ≤ α₀ l ∧ α₀ l + β₀ l ≤ 1 ∧
        ∀ i, ContDiffOn ℝ r (fun t : ℝ => F i l (α₀ l + β₀ l * t)) I ∧
          ∀ m ≤ r, ∀ t ∈ I,
            |iteratedDeriv m (fun t : ℝ => F i l (α₀ l + β₀ l * t)) t| ≤ 1 := by
      simpa only [Chart1] using hφ₀
    exact ⟨h1, h2, h3⟩
  -- The per-cell chart families: for a good cell, the cell's own charts glued with the global
  -- chart `φ₀` (`HC`), for a degenerate cell the empty family.  Then `Φ := ⋃_σ Φ_σ`.
  have hex : ∀ σ : Fin m, ∃ Φσ : Finset (((Fin p → ℝ) → ℝ) × ((Fin p → ℝ) → ℝ)),
      ((Φσ.card : ℝ) ≤
        max 0 (MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] cA')) ∧
      ChartFam S p aA (MvPolynomial.eval ![D, r] bA) Λ k r F Φσ ∧
      (∀ l ∈ Λ, ¬ (Work.WilG4a.fibre (κ σ) l).Subsingleton →
        ∀ x ∈ Work.WilG4a.fibre (κ σ) l,
          ∃ αβ ∈ Φσ, ∃ t ∈ Work.WilG4a.I, |αβ.1 l + αβ.2 l * t - x| < ε / 2) := by
    intro σ
    rcases hκdich σ with hg | hd
    · obtain ⟨Φσ, hcard, hfam, hcov⟩ := hA D r k (ε / 2) (by linarith) (by linarith) Λ F
        (κ σ) α₀ β₀ hFΩ hFI hg (hκΩ' σ) hα₀' hβ₀' hφ₀'
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
      obtain ⟨αβ, hαβ, t, ht, hcov⟩ := (hΦσ τ).2.2 l hl hndτ y hy
      refine ⟨αβ, Finset.mem_biUnion.mpr ⟨τ, Finset.mem_univ τ, hαβ⟩, t, ht, ?_⟩
      have htri : |αβ.1 l + αβ.2 l * t - x| ≤
          |αβ.1 l + αβ.2 l * t - y| + |y - x| := by
        have h := abs_add_le (αβ.1 l + αβ.2 l * t - y) (y - x)
        rwa [show αβ.1 l + αβ.2 l * t - y + (y - x) = αβ.1 l + αβ.2 l * t - x by ring] at h
      linarith
    · -- nondegenerate fibre: the cell's own charts cover `x` up to `ε/2 < ε`
      obtain ⟨αβ, hαβ, t, ht, hcov⟩ := (hΦσ σ).2.2 l hl hnd x hσ
      exact ⟨αβ, Finset.mem_biUnion.mpr ⟨σ, Finset.mem_univ σ, hαβ⟩, t, ht,
        lt_of_lt_of_le hcov (by linarith)⟩

/-
  RETIRED (lead audit `sources/wilkiesG4/wilkies_g4_audit.md`, 2026-10-11): the theorem
  `f1affine1_of_signConst` that was stated here — the frozen `F1Affine1 S p` in `ℝ`-coordinates
  — is FALSE at `p = 1`, so it cannot be proved.  The corrected target is `F1Affine1W`
  (`F1Affine1W.lean`), and the replacement result `f1affine1W_all`
  (`f1affine1W_all.lean`) is proved there.  The supporting lemmas above (the cell
  decomposition, the `Ω`-bookkeeping and the per-cell chart constructions) are kept, since
  the corrected proof builds on them.
-/

end Work.WilG4a
