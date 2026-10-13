/-
  WilG4a — the `n = 1` family lemma `FLem1` from its parts, with the *corrected* affine
  input `F1Affine1W` (`β ≥ 0` allowed on the charts, `β > 0` only on the charts that do the
  `ε`-covering).

  The assembly `Work.WilG4a.fleem1_of_parts_of_lip` (in `Submission/Work/WilG4a/
  fleem1_of_parts.lean`) is insensitive to which affine corollary is fed into its `1`-Lipschitz
  slot: it uses the corollary only through (i) the per-chart `C^r` bounds (which it copies) and
  (ii) the `ε`-cover of the *domain* `I`, which it converts into an `ε`-cover of the *image*
  using `1`-Lipschitzness of the family (`lip_of_deriv_le_one`).

  The only input of the frozen `lip_case_flem1` that the corrected `F1Affine1W` does not supply
  is `0 < αβ.2 l` for *all* charts; the corrected statement supplies it only for the charts used
  in the cover, which is exactly what the cover argument needs.  Otherwise the two proofs are
  identical: `F1Affine1W` even carries the image condition `∀ t ∈ I, αβ.1 l + αβ.2 l * t ∈ I`
  as a hypothesis, so no `affine_mem_I` computation is required.

  This file proves

  * `lip_case_flem1_W` — the `1`-Lipschitz case of `FLem1` from `F1Affine1W` and the
    `Ω`-definability of affine charts (`hAC`),
  * `fleem1_of_parts_W` — the requested assembly, obtained by feeding `lip_case_flem1_W` into
    `fleem1_of_parts_of_lip`.
-/
import Mathlib
import Submission.Work.WilG4a.Defs
import Submission.Work.WilG4a.Cells
import Submission.Work.WilG4a.F1Affine1W
import Submission.Work.WilG4a.ChartUnion
import Submission.Work.WilG4a.Bounds
import Submission.Work.WilG4a.fleem1_of_parts
import Submission.Work.WilG4a.affineChart_graph_mem

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilG4a

open WilkiesConjecture WilkiesDesign

/-- **The `1`-Lipschitz case of the `n = 1` family lemma, corrected version.**

When every member of the family is `C^1` on `I` with derivative bounded by `1`, the corrected
affine corollary `hFA : ∀ p, F1Affine1W S p` produces charts `αβ` of the prescribed shape.
Their graphs are `Ω`-definable by `hAC`; the composite derivative bounds are part of `hFA`'s
conclusion; and the `ε`-cover of the domain, upgraded to an `ε`-cover of the image by
`1`-Lipschitzness, is achieved by the charts with `0 < αβ.2 l` — which is precisely the
condition that `F1Affine1W` attaches to the covering charts. -/
theorem lip_case_flem1_W (S : WilkiesDesign.SOMin)
    (hFA : ∀ p : ℕ, Work.WilG4a.F1Affine1W S p)
    (hAC : ∀ (p F : ℕ), ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ),
      ∀ (D r : ℕ) {α β : (Fin p → ℝ) → ℝ},
        WilkiesDesign.graphOf α ∈ S.Ω F D (p + 1) →
        WilkiesDesign.graphOf β ∈ S.Ω F D (p + 1) →
        Work.WilG4a.graphFam (fun l (t : ℝ) => α l + β l * t) ∈
          S.Ω a (MvPolynomial.eval ![D, r] b) (p + 1 + 1))
    (p F0 : ℕ) :
    ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ) (c : MvPolynomial (Fin 4) ℝ),
      ∀ (D r k : ℕ) (ε : ℝ), 0 < ε → ε < 1 →
      ∀ (Λ : Set (Fin p → ℝ)) (F : Fin k → (Fin p → ℝ) → ℝ → ℝ),
        (∀ i, Work.WilG4a.graphFam (F i) ∈ S.Ω F0 D (p + 1 + 1)) →
        (∀ i, ∀ l ∈ Λ, ∀ x ∈ Work.WilG4a.I, F i l x ∈ Work.WilG4a.I) →
        (∀ i, ∀ l ∈ Λ, ContDiffOn ℝ 1 (fun t : ℝ => F i l t) Work.WilG4a.I ∧
          ∀ t ∈ Work.WilG4a.I, |iteratedDeriv 1 (fun t : ℝ => F i l t) t| ≤ 1) →
        ∃ Φ : Finset ((Fin p → ℝ) → ℝ → ℝ),
          (Φ.card : ℝ) ≤ MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] c ∧
          (∀ φ ∈ Φ, Work.WilG4a.ChartOK S a (MvPolynomial.eval ![D, r] b) Λ k r F φ) ∧
          Work.WilG4a.Covers Λ k F Φ ε := by
  -- BNZ Cor. 5.5 for this family (corrected form), and `Ω`-definability of the affine graphs
  obtain ⟨a0, b0, c0, h0⟩ := hFA p F0
  obtain ⟨a1, b1, h1⟩ := hAC p a0
  obtain ⟨b1', hb1'⟩ := exists_eval_comp b1 b0
  refine ⟨a1, b1', c0, ?_⟩
  intro D r k ε hε0 hε1 Λ F hΩ hI hLipF
  obtain ⟨Φ0, hcard0, hprop0, hcov0⟩ := h0 D r k ε hε0 hε1 Λ F hΩ hI
  refine ⟨Φ0.image (fun αβ => fun l t => αβ.1 l + αβ.2 l * t), ?_, ?_, ?_⟩
  · -- the number of charts
    refine le_trans ?_ hcard0
    exact_mod_cast Finset.card_image_le
  · -- the per-chart conditions
    intro ψ hψ
    rw [Finset.mem_image] at hψ
    obtain ⟨αβ, hαβ, rfl⟩ := hψ
    obtain ⟨hα, hβ, hrest⟩ := hprop0 αβ hαβ
    refine ⟨?_, ?_⟩
    · have h := h1 (MvPolynomial.eval ![D, r] b0) r hα hβ
      rwa [hb1' D r] at h
    · intro l hl
      refine ⟨?_, ?_⟩
      · intro t ht
        exact (hrest l hl).2.2.2.1 t ht
      · intro i
        exact (hrest l hl).2.2.2.2 i
  · -- the `ε`-cover of the image
    intro l hl x hx
    obtain ⟨αβ, hαβ, -, t, ht, hlt⟩ := hcov0 l hl x hx
    obtain ⟨-, -, hrest⟩ := hprop0 αβ hαβ
    have hu : αβ.1 l + αβ.2 l * t ∈ I := (hrest l hl).2.2.2.1 t ht
    refine ⟨fun l t => αβ.1 l + αβ.2 l * t, ?_, t, ht, ?_⟩
    · exact Finset.mem_image.mpr ⟨αβ, hαβ, rfl⟩
    · intro i
      have hg := hLipF i l hl
      have hlip := lip_of_deriv_le_one hg.1 hg.2 x hx (αβ.1 l + αβ.2 l * t) hu
      linarith

theorem fleem1_of_parts_W (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv) (hLip : ∀ (p F0 : ℕ), ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ) (cc : MvPolynomial (Fin 3) ℝ), ∀ (D k : ℕ) (Λ : Set (Fin p → ℝ)) (F : Fin k → (Fin p → ℝ) → ℝ → ℝ), (∀ i, Work.WilG4a.graphFam (F i) ∈ S.Ω F0 D (p + 1 + 1)) → (∀ i, ∀ l ∈ Λ, ∀ x ∈ Work.WilG4a.I, F i l x ∈ Work.WilG4a.I) → ∃ (m : ℕ), (m : ℝ) ≤ MvPolynomial.eval ![(D : ℝ), (1 : ℝ), (k : ℝ)] cc ∧ ∃ (φ : Fin m → (Fin p → ℝ) → ℝ → ℝ), (∀ η, Work.WilG4a.graphFam (φ η) ∈ S.Ω a (MvPolynomial.eval ![D, 1] b) (p + 1 + 1)) ∧ (∀ η l, l ∈ Λ → ∀ t ∈ Work.WilG4a.I, φ η l t ∈ Work.WilG4a.I) ∧ (∀ η (i : Fin k) (l : Fin p → ℝ), l ∈ Λ → ContDiffOn ℝ 1 (fun t : ℝ => F i l (φ η l t)) Work.WilG4a.I ∧ ∀ t ∈ Work.WilG4a.I, |iteratedDeriv 1 (fun t : ℝ => F i l (φ η l t)) t| ≤ 1) ∧ (∀ l ∈ Λ, ∀ x ∈ Work.WilG4a.I, ∃ η, ∃ t ∈ Work.WilG4a.I, φ η l t = x)) (hPB : ∀ (p F : ℕ), ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ), ∀ (D r : ℕ) {φ f : (Fin p → ℝ) → ℝ → ℝ}, Work.WilG4a.graphFam φ ∈ S.Ω F D (p + 1 + 1) → Work.WilG4a.graphFam f ∈ S.Ω F D (p + 1 + 1) → Work.WilG4a.graphFam (fun l t => f l (φ l t)) ∈ S.Ω a (MvPolynomial.eval ![D, r] b) (p + 1 + 1)) (hFA : ∀ p : ℕ, Work.WilG4a.F1Affine1W S p) (hAC : ∀ (p : ℕ) (F' : ℕ), ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ), ∀ (D r : ℕ) {α β : (Fin p → ℝ) → ℝ}, WilkiesDesign.graphOf α ∈ S.Ω F' D (p + 1) → WilkiesDesign.graphOf β ∈ S.Ω F' D (p + 1) → Work.WilG4a.graphFam (fun l (t : ℝ) => α l + β l * t) ∈ S.Ω a (MvPolynomial.eval ![D, r] b) (p + 1 + 1)) (p : ℕ) : Work.WilG4a.FLem1 S p :=
  -- The assembly `fleem1_of_parts_of_lip` is exactly the paper's BNZ §5.1 argument; the only
  -- input that had to be replaced for the corrected affine statement is the `1`-Lipschitz case.
  fleem1_of_parts_of_lip S hLip hPB
    (fun (p : ℕ) (F0 : ℕ) => lip_case_flem1_W S hFA hAC p F0) p

end Work.WilG4a
