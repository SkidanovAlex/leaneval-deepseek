import Submission.Work.Wilkies.CG.Spec

/-! LEAD-OWNED (curric-46, 2026-10-11; cbc/wilkies_g4_audit.md + wilkies_g4_REVIEW.md). Do not edit. The frozen F1Affine is FALSE at p = 1; F1AffineW is the corrected target. -/

set_option autoImplicit false
noncomputable section
namespace Work.WilG4a
open WilkiesDesign WilkiesDesign.CG

/-- BNZ Cor 5.5, CORRECTED: as `CG.F1Affine`, but a chart may be degenerate (`β l = 0`, the
constant chart `t ↦ α l`) at some parameters; the cover must be achieved by non-degenerate
charts. -/
def F1AffineW (S : SOMin) (p : ℕ) : Prop :=
  ∀ F0 : ℕ, ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ) (c : MvPolynomial (Fin 4) ℝ),
    ∀ (D r k : ℕ) (ε : ℝ), 0 < ε → ε < 1 →
    ∀ (Λ : Set (Fin p → ℝ)) (F : Fin k → (Fin p → ℝ) → (Fin 1 → ℝ) → ℝ),
      (∀ i, famGraph (F i) ∈ S.Ω F0 D (p + 1 + 1)) →
      (∀ i, ∀ l ∈ Λ, ∀ x ∈ openCube 1, F i l x ∈ Set.Ioo (0 : ℝ) 1) →
      ∃ Φ : Finset (((Fin p → ℝ) → ℝ) × ((Fin p → ℝ) → ℝ)),
        (Φ.card : ℝ) ≤ MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] c ∧
        (∀ αβ ∈ Φ, graphOf αβ.1 ∈ S.Ω a (MvPolynomial.eval ![D, r] b) (p + 1) ∧
          graphOf αβ.2 ∈ S.Ω a (MvPolynomial.eval ![D, r] b) (p + 1) ∧
          ∀ l ∈ Λ, 0 ≤ αβ.2 l ∧ 0 ≤ αβ.1 l ∧ αβ.1 l + αβ.2 l ≤ 1 ∧
            (∀ t ∈ Set.Ioo (0 : ℝ) 1, αβ.1 l + αβ.2 l * t ∈ Set.Ioo (0 : ℝ) 1) ∧
            ∀ i, ContDiffOn ℝ r (fun t : Fin 1 → ℝ => F i l (fun _ => αβ.1 l + αβ.2 l * t 0))
                (openCube 1) ∧
              ∀ m ≤ r, ∀ t ∈ openCube 1, ‖iteratedFDeriv ℝ m
                (fun t : Fin 1 → ℝ => F i l (fun _ => αβ.1 l + αβ.2 l * t 0)) t‖ ≤ 1) ∧
        ∀ l ∈ Λ, ∀ x ∈ Set.Ioo (0 : ℝ) 1, ∃ αβ ∈ Φ, 0 < αβ.2 l ∧
          ∃ t ∈ Set.Ioo (0 : ℝ) 1, |αβ.1 l + αβ.2 l * t - x| < ε

/-- The frozen `F1Affine` implies the corrected one (it is a pure weakening). -/
theorem F1AffineW_of_F1Affine (S : SOMin) (p : ℕ) (h : F1Affine S p) : F1AffineW S p := by
  intro F0
  obtain ⟨a, b, c, hc⟩ := h F0
  refine ⟨a, b, c, ?_⟩
  intro D r k ε hε hε1 Λ F hF hI
  obtain ⟨Φ, hcard, hch, hcov⟩ := hc D r k ε hε hε1 Λ F hF hI
  refine ⟨Φ, hcard, ?_, ?_⟩
  · intro αβ hαβ
    obtain ⟨h1, h2, h3⟩ := hch αβ hαβ
    refine ⟨h1, h2, fun l hl => ?_⟩
    obtain ⟨hb, ha, hab, hrest⟩ := h3 l hl
    refine ⟨hb.le, ha, hab, fun t ht => ⟨?_, ?_⟩, hrest⟩
    · have := mul_pos hb ht.1; linarith
    · have : αβ.2 l * t < αβ.2 l * 1 := mul_lt_mul_of_pos_left ht.2 hb
      linarith
  · intro l hl x hx
    obtain ⟨αβ, hαβ, t, ht, hlt⟩ := hcov l hl x hx
    exact ⟨αβ, hαβ, ((hch αβ hαβ).2.2 l hl).1, t, ht, hlt⟩

/-- The universal fallback chart `(α, β) = (1/2, 0)` satisfies every per-chart condition of
`F1AffineW` (for any family with values in `(0,1)` on `Λ`), independently of `k`. -/
theorem fallback_chart_ok {p k : ℕ} (r : ℕ) (Λ : Set (Fin p → ℝ))
    (F : Fin k → (Fin p → ℝ) → (Fin 1 → ℝ) → ℝ)
    (hI : ∀ i, ∀ l ∈ Λ, ∀ x ∈ openCube 1, F i l x ∈ Set.Ioo (0 : ℝ) 1) :
    ∀ l ∈ Λ, (0 : ℝ) ≤ 0 ∧ (0 : ℝ) ≤ 1 / 2 ∧ (1 / 2 : ℝ) + 0 ≤ 1 ∧
      (∀ t ∈ Set.Ioo (0 : ℝ) 1, (1 / 2 : ℝ) + 0 * t ∈ Set.Ioo (0 : ℝ) 1) ∧
      ∀ i, ContDiffOn ℝ r (fun t : Fin 1 → ℝ => F i l (fun _ => (1 / 2 : ℝ) + 0 * t 0))
          (openCube 1) ∧
        ∀ m ≤ r, ∀ t ∈ openCube 1, ‖iteratedFDeriv ℝ m
          (fun t : Fin 1 → ℝ => F i l (fun _ => (1 / 2 : ℝ) + 0 * t 0)) t‖ ≤ 1 := by
  intro l hl
  refine ⟨le_rfl, by norm_num, by norm_num, fun t _ => by norm_num, fun i => ?_⟩
  have hconst : (fun t : Fin 1 → ℝ => F i l (fun _ => (1 / 2 : ℝ) + 0 * t 0))
      = fun _ => F i l (fun _ => 1 / 2) := by
    funext t; simp
  have hmem : (fun _ : Fin 1 => (1 / 2 : ℝ)) ∈ openCube 1 := by
    intro j; norm_num
  have hv := hI i l hl _ hmem
  rw [hconst]
  refine ⟨contDiffOn_const, fun m _ t _ => ?_⟩
  rcases Nat.eq_zero_or_pos m with h0 | hpos
  · subst h0
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs, abs_le]
    constructor <;> linarith [hv.1, hv.2]
  · rw [iteratedFDeriv_const_of_ne (Nat.pos_iff_ne_zero.mp hpos)]
    simp

/-- The fallback chart graphs are `Ω`-definable with `k`-independent format/degree. -/
theorem graphOf_const_mem_W (S : SOMin) (p : ℕ) (q : ℝ) :
    graphOf (fun _ : Fin p → ℝ => q) ∈ S.Ω (p + 1) 1 (p + 1) := by
  have h := S.hyp (p + 1) (MvPolynomial.X (Fin.last p) - MvPolynomial.C q)
  have hdeg : (MvPolynomial.X (Fin.last p) - MvPolynomial.C q :
      MvPolynomial (Fin (p + 1)) ℝ).totalDegree ≤ 1 := by
    refine (MvPolynomial.totalDegree_sub _ _).trans ?_
    simp [MvPolynomial.totalDegree_X, MvPolynomial.totalDegree_C]
  have hset : {x : Fin (p + 1) → ℝ | MvPolynomial.eval x
      (MvPolynomial.X (Fin.last p) - MvPolynomial.C q) = 0} = graphOf (fun _ => q) := by
    ext z; simp [graphOf, sub_eq_zero]
  rw [hset] at h
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hdeg with h0 | h1
  · rw [h0] at h; exact S.mono_D h
  · rw [h1] at h; exact h

end Work.WilG4a
