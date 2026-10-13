/-
  WilG4a — BNZ §5.1 (`n = 1`): the family lemma `FLem1` from its parts.

  This module proves `Work.WilG4a.fleem1_of_parts`.  Its proof is the argument of BNZ §5.1:

  * `hLip` (BNZ Lemma 5.3, `full-C1`) supplies an exact cover of `I` by `Ω`-definable charts
    `φ_η` along which the family is `C^1` with derivative bounded by `1`;
  * pulling the family back along each `φ_η` (the composition rule `hPB`) gives families that
    are `1`-Lipschitz;
  * `hD3` is the `1`-Lipschitz case of the family lemma: BNZ Cor. 5.5 (`F1Affine1`, hypothesis
    `hFA`) gives affine charts `A` whose graphs are `Ω`-definable (`hAC`), the composite
    `F ∘ A` has all derivative norms `≤ 1` up to order `r`, and the domain cover becomes an
    image cover because the family is `1`-Lipschitz;
  * composing those charts with `φ_η` (again `hPB`) produces the charts required by `FLem1`;
  * the counts multiply and the degrees compose, which is the polynomial bookkeeping below.

  The final `fleem1_of_parts` instantiates `hD3` with the module `flem1_lip_aux` and `hAC`
  with the module `affineChart_graph_mem`.
-/
import Mathlib
import Submission.Work.WilG4a.Defs
import Submission.Work.WilG4a.Cells
import Submission.Work.WilG4a.ChartUnion
import Submission.Work.WilG4a.Bounds
import Submission.Work.WilG5.Basic
import Submission.Work.WilG4a.affineChart_graph_mem

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilG4a

open WilkiesConjecture WilkiesDesign

/-! ## Polynomial substitution bookkeeping -/

/-- Substituting the second variable by `1`: `b.eval ![D,1]` is again the evaluation of a
`Fin 2`-polynomial, now at `![D,r]` (with `r` arbitrary). -/
theorem exists_eval_second_one (b : MvPolynomial (Fin 2) ℕ) :
    ∃ d : MvPolynomial (Fin 2) ℕ, ∀ D r : ℕ,
      MvPolynomial.eval ![D, 1] b = MvPolynomial.eval ![D, r] d := by
  refine ⟨MvPolynomial.bind₁ (fun i : Fin 2 =>
    if i = 0 then MvPolynomial.X (0 : Fin 2) else MvPolynomial.C (1 : ℕ)) b, ?_⟩
  intro D r
  have h := MvPolynomial.eval₂Hom_bind₁ (RingHom.id ℕ) ![D, r]
    (fun i : Fin 2 => if i = 0 then MvPolynomial.X (0 : Fin 2) else MvPolynomial.C (1 : ℕ)) b
  have hfun : (fun i : Fin 2 => MvPolynomial.eval₂Hom (RingHom.id ℕ) ![D, r]
      (if i = 0 then MvPolynomial.X (0 : Fin 2) else MvPolynomial.C (1 : ℕ))) = ![D, 1] := by
    funext i
    fin_cases i <;> simp
  rw [hfun] at h
  change MvPolynomial.eval₂Hom (RingHom.id ℕ) ![D, 1] b
    = MvPolynomial.eval₂Hom (RingHom.id ℕ) ![D, r]
        (MvPolynomial.bind₁ (fun i : Fin 2 =>
          if i = 0 then MvPolynomial.X (0 : Fin 2) else MvPolynomial.C (1 : ℕ)) b)
  exact h.symm

/-- The sum `D + b.eval ![D,1]` is the evaluation of a single `Fin 2`-polynomial at `![D,r]`. -/
theorem exists_eval_add_fst_one (b : MvPolynomial (Fin 2) ℕ) :
    ∃ d : MvPolynomial (Fin 2) ℕ, ∀ D r : ℕ,
      MvPolynomial.eval ![D, r] d = D + MvPolynomial.eval ![D, 1] b := by
  obtain ⟨d₁, hd₁⟩ := exists_eval_second_one b
  refine ⟨MvPolynomial.X (0 : Fin 2) + d₁, ?_⟩
  intro D r
  rw [MvPolynomial.eval_add, MvPolynomial.eval_X, hd₁ D r]
  rfl

/-- For natural-coefficient polynomials, the real evaluation of the polynomial with real
coefficients is the coercion of the natural evaluation. -/
theorem eval₂Hom_natCast_cast {n : ℕ} (g : Fin n → ℕ) (p : MvPolynomial (Fin n) ℕ) :
    MvPolynomial.eval₂Hom (Nat.castRingHom ℝ) (fun i : Fin n => ((g i : ℕ) : ℝ)) p
      = ((MvPolynomial.eval₂Hom (RingHom.id ℕ) g p : ℕ) : ℝ) := by
  refine RingHom.congr_fun (MvPolynomial.ringHom_ext (σ := Fin n) (R := ℕ) (A := ℝ)
    (f := MvPolynomial.eval₂Hom (Nat.castRingHom ℝ) (fun i : Fin n => ((g i : ℕ) : ℝ)))
    (g := (Nat.castRingHom ℝ).comp (MvPolynomial.eval₂Hom (RingHom.id ℕ) g)) ?_ ?_) p
  · intro a
    simp only [MvPolynomial.eval₂Hom_C, RingHom.comp_apply, RingHom.id_apply]
  · intro i
    simp only [MvPolynomial.eval₂Hom_X', RingHom.comp_apply, RingHom.id_apply]
    rfl

/-- **Substituting a polynomial bound into the first variable.**  The value at
`![b.eval ![D,r], r, k, L]` of a polynomial in `4` variables is again the value at
`![D, r, k, L]` of a polynomial in `4` variables. -/
theorem exists_eval_sub_first (b : MvPolynomial (Fin 2) ℕ) (c : MvPolynomial (Fin 4) ℝ) :
    ∃ c' : MvPolynomial (Fin 4) ℝ, ∀ D r k : ℕ, ∀ L : ℝ,
      MvPolynomial.eval ![(MvPolynomial.eval ![D, r] b : ℝ), (r : ℝ), (k : ℝ), L] c
        = MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), L] c' := by
  -- the polynomial in `X 0, X 1` whose value at `![D,r]` is the coerced `b.eval ![D,r]`
  let B' : MvPolynomial (Fin 4) ℝ :=
    MvPolynomial.rename (fun i : Fin 2 => if i = 0 then (0 : Fin 4) else (1 : Fin 4))
      (MvPolynomial.map (Nat.castRingHom ℝ) b)
  have hB'eval : ∀ D r k : ℕ, ∀ L : ℝ,
      MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), L] B'
        = ((MvPolynomial.eval ![D, r] b : ℕ) : ℝ) := by
    intro D r k L
    have hρ : (![(D : ℝ), (r : ℝ), (k : ℝ), L]) ∘
        (fun i : Fin 2 => if i = 0 then (0 : Fin 4) else (1 : Fin 4))
        = fun i : Fin 2 => ((![D, r] i : ℕ) : ℝ) := by
      funext i
      fin_cases i <;> simp
    calc MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), L] B'
        = MvPolynomial.eval₂Hom (RingHom.id ℝ) ![(D : ℝ), (r : ℝ), (k : ℝ), L]
            (MvPolynomial.rename (fun i : Fin 2 => if i = 0 then (0 : Fin 4) else (1 : Fin 4))
              (MvPolynomial.map (Nat.castRingHom ℝ) b)) := rfl
      _ = MvPolynomial.eval₂Hom (RingHom.id ℝ)
            (![(D : ℝ), (r : ℝ), (k : ℝ), L] ∘
              (fun i : Fin 2 => if i = 0 then (0 : Fin 4) else (1 : Fin 4)))
            (MvPolynomial.map (Nat.castRingHom ℝ) b) :=
          MvPolynomial.eval₂Hom_rename (f := RingHom.id ℝ) _ _ _
      _ = MvPolynomial.eval₂Hom (Nat.castRingHom ℝ)
            (![(D : ℝ), (r : ℝ), (k : ℝ), L] ∘
              (fun i : Fin 2 => if i = 0 then (0 : Fin 4) else (1 : Fin 4))) b := by
          rw [MvPolynomial.eval₂Hom_map_hom, RingHom.id_comp]
      _ = MvPolynomial.eval₂Hom (Nat.castRingHom ℝ)
            (fun i : Fin 2 => ((![D, r] i : ℕ) : ℝ)) b := by rw [hρ]
      _ = ((MvPolynomial.eval₂Hom (RingHom.id ℕ) ![D, r] b : ℕ) : ℝ) :=
          eval₂Hom_natCast_cast ![D, r] b
      _ = ((MvPolynomial.eval ![D, r] b : ℕ) : ℝ) := rfl
  refine ⟨MvPolynomial.bind₁ (fun i : Fin 4 =>
    if i = 0 then B' else MvPolynomial.X i) c, ?_⟩
  intro D r k L
  have h := MvPolynomial.eval₂Hom_bind₁ (RingHom.id ℝ) ![(D : ℝ), (r : ℝ), (k : ℝ), L]
    (fun i : Fin 4 => if i = 0 then B' else MvPolynomial.X i) c
  have hfun : (fun i : Fin 4 => MvPolynomial.eval₂Hom (RingHom.id ℝ)
      ![(D : ℝ), (r : ℝ), (k : ℝ), L]
      (if i = 0 then B' else MvPolynomial.X i))
      = ![(MvPolynomial.eval ![D, r] b : ℝ), (r : ℝ), (k : ℝ), L] := by
    funext i
    fin_cases i <;> simp [hB'eval D r k L]
  rw [hfun] at h
  change MvPolynomial.eval₂Hom (RingHom.id ℝ)
      ![(MvPolynomial.eval ![D, r] b : ℝ), (r : ℝ), (k : ℝ), L] c
    = MvPolynomial.eval₂Hom (RingHom.id ℝ) ![(D : ℝ), (r : ℝ), (k : ℝ), L]
        (MvPolynomial.bind₁ (fun i : Fin 4 =>
          if i = 0 then B' else MvPolynomial.X i) c)
  exact h.symm

/-- Embedding a bound in `3` variables (with the second variable set to `1`) as a bound in `4`
variables (with an unused fourth variable). -/
theorem exists_eval_F3_to_F4 (cc : MvPolynomial (Fin 3) ℝ) :
    ∃ c : MvPolynomial (Fin 4) ℝ, ∀ D r k : ℕ, ∀ L : ℝ,
      MvPolynomial.eval ![(D : ℝ), (1 : ℝ), (k : ℝ)] cc
        = MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), L] c := by
  refine ⟨MvPolynomial.bind₁ (fun i : Fin 3 =>
    if i = 0 then MvPolynomial.X (0 : Fin 4)
      else if i = 1 then MvPolynomial.C (1 : ℝ) else MvPolynomial.X (2 : Fin 4)) cc, ?_⟩
  intro D r k L
  have h := MvPolynomial.eval₂Hom_bind₁ (RingHom.id ℝ) ![(D : ℝ), (r : ℝ), (k : ℝ), L]
    (fun i : Fin 3 => if i = 0 then MvPolynomial.X (0 : Fin 4)
      else if i = 1 then MvPolynomial.C (1 : ℝ) else MvPolynomial.X (2 : Fin 4)) cc
  have hfun : (fun i : Fin 3 => MvPolynomial.eval₂Hom (RingHom.id ℝ)
      ![(D : ℝ), (r : ℝ), (k : ℝ), L]
      (if i = 0 then MvPolynomial.X (0 : Fin 4)
        else if i = 1 then MvPolynomial.C (1 : ℝ) else MvPolynomial.X (2 : Fin 4)))
      = ![(D : ℝ), (1 : ℝ), (k : ℝ)] := by
    funext i
    fin_cases i <;> simp
  rw [hfun] at h
  change MvPolynomial.eval₂Hom (RingHom.id ℝ) ![(D : ℝ), (1 : ℝ), (k : ℝ)] cc
    = MvPolynomial.eval₂Hom (RingHom.id ℝ) ![(D : ℝ), (r : ℝ), (k : ℝ), L]
        (MvPolynomial.bind₁ (fun i : Fin 3 => if i = 0 then MvPolynomial.X (0 : Fin 4)
          else if i = 1 then MvPolynomial.C (1 : ℝ) else MvPolynomial.X (2 : Fin 4)) cc)
  exact h.symm

/-! ## The assembly -/

/-- **The `n = 1` family lemma from its parts.**  `hLip` is BNZ Lemma 5.3, `hPB` the pullback
rule for `Ω`-graphs, and `hD3` the `1`-Lipschitz case of the family lemma (which is where
BNZ Cor. 5.5 is used). -/
theorem fleem1_of_parts_of_lip (S : WilkiesDesign.SOMin)
    (hLip : ∀ (p F0 : ℕ),
      ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ) (cc : MvPolynomial (Fin 3) ℝ),
        ∀ (D k : ℕ) (Λ : Set (Fin p → ℝ)) (F : Fin k → (Fin p → ℝ) → ℝ → ℝ),
          (∀ i, Work.WilG4a.graphFam (F i) ∈ S.Ω F0 D (p + 1 + 1)) →
          (∀ i, ∀ l ∈ Λ, ∀ x ∈ Work.WilG4a.I, F i l x ∈ Work.WilG4a.I) →
          ∃ (m : ℕ), (m : ℝ) ≤ MvPolynomial.eval ![(D : ℝ), (1 : ℝ), (k : ℝ)] cc ∧
            ∃ (φ : Fin m → (Fin p → ℝ) → ℝ → ℝ),
              (∀ η, Work.WilG4a.graphFam (φ η) ∈
                S.Ω a (MvPolynomial.eval ![D, 1] b) (p + 1 + 1)) ∧
              (∀ η l, l ∈ Λ → ∀ t ∈ Work.WilG4a.I, φ η l t ∈ Work.WilG4a.I) ∧
              (∀ η (i : Fin k) (l : Fin p → ℝ), l ∈ Λ →
                ContDiffOn ℝ 1 (fun t : ℝ => F i l (φ η l t)) Work.WilG4a.I ∧
                  ∀ t ∈ Work.WilG4a.I,
                    |iteratedDeriv 1 (fun t : ℝ => F i l (φ η l t)) t| ≤ 1) ∧
              (∀ l ∈ Λ, ∀ x ∈ Work.WilG4a.I, ∃ η, ∃ t ∈ Work.WilG4a.I, φ η l t = x))
    (hPB : ∀ (p F : ℕ), ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ),
      ∀ (D r : ℕ) {φ f : (Fin p → ℝ) → ℝ → ℝ},
        Work.WilG4a.graphFam φ ∈ S.Ω F D (p + 1 + 1) →
          Work.WilG4a.graphFam f ∈ S.Ω F D (p + 1 + 1) →
          Work.WilG4a.graphFam (fun l t => f l (φ l t)) ∈
            S.Ω a (MvPolynomial.eval ![D, r] b) (p + 1 + 1))
    (hD3 : ∀ (p F0 : ℕ), ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ) (c : MvPolynomial (Fin 4) ℝ),
      ∀ (D r k : ℕ) (ε : ℝ), 0 < ε → ε < 1 →
      ∀ (Λ : Set (Fin p → ℝ)) (F : Fin k → (Fin p → ℝ) → ℝ → ℝ),
        (∀ i, Work.WilG4a.graphFam (F i) ∈ S.Ω F0 D (p + 1 + 1)) →
        (∀ i, ∀ l ∈ Λ, ∀ x ∈ Work.WilG4a.I, F i l x ∈ Work.WilG4a.I) →
        (∀ i, ∀ l ∈ Λ, ContDiffOn ℝ 1 (fun t : ℝ => F i l t) Work.WilG4a.I ∧
          ∀ t ∈ Work.WilG4a.I, |iteratedDeriv 1 (fun t : ℝ => F i l t) t| ≤ 1) →
        ∃ Φ : Finset ((Fin p → ℝ) → ℝ → ℝ),
          (Φ.card : ℝ) ≤ MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] c ∧
          (∀ φ ∈ Φ, Work.WilG4a.ChartOK S a (MvPolynomial.eval ![D, r] b) Λ k r F φ) ∧
          Work.WilG4a.Covers Λ k F Φ ε)
    (p : ℕ) : Work.WilG4a.FLem1 S p := by
  intro F0
  -- Lipschitz preparation
  obtain ⟨aLip, bLip, ccLip, hLipSpec⟩ := hLip p F0
  obtain ⟨d1, hd1⟩ := exists_eval_second_one bLip
  obtain ⟨dD, hdD⟩ := exists_eval_add_fst_one bLip
  -- the format/degree of the pulled-back families
  obtain ⟨aPB, bPB, hPBSpec⟩ := hPB p (max F0 aLip)
  obtain ⟨b2, hb2⟩ := exists_eval_comp bPB dD
  -- the `1`-Lipschitz case at the format of the pulled-back families
  obtain ⟨a3, b3, c3, hD3spec⟩ := hD3 p aPB
  obtain ⟨b3', hb3'⟩ := exists_eval_comp b3 b2
  obtain ⟨c3', hc3'⟩ := exists_eval_sub_first b2 c3
  -- the final composition
  obtain ⟨a4, b4, hPBSpec2⟩ := hPB p (max a3 aLip)
  obtain ⟨b4', hb4'⟩ := exists_eval_comp b4 (b3' + d1)
  -- the count bound
  obtain ⟨c1, hc1⟩ := exists_eval_F3_to_F4 ccLip
  refine ⟨a4, b4', c1 * c3' + (c1 * c3') * (c1 * c3') + 1, ?_⟩
  intro D r k ε hε0 hε1 Λ F hΩ hI
  obtain ⟨m, hm, φ, hφgraph, hφin, hφlip, hφcov⟩ := hLipSpec D k Λ F hΩ hI
  -- the pulled-back families are Ω-definable
  have hGΩ : ∀ η : Fin m, ∀ i : Fin k,
      Work.WilG4a.graphFam (fun l t => F i l (φ η l t)) ∈
        S.Ω aPB (MvPolynomial.eval ![D, r] b2) (p + 1 + 1) := by
    intro η i
    have h1 : Work.WilG4a.graphFam (φ η) ∈
        S.Ω (max F0 aLip) (D + MvPolynomial.eval ![D, 1] bLip) (p + 1 + 1) :=
      Work.WilG5.mem_mono (hφgraph η) _ _ (le_max_right _ _) (by omega)
    have h2 : Work.WilG4a.graphFam (F i) ∈
        S.Ω (max F0 aLip) (D + MvPolynomial.eval ![D, 1] bLip) (p + 1 + 1) :=
      Work.WilG5.mem_mono (hΩ i) _ _ (le_max_left _ _) (by omega)
    have h3 := hPBSpec (D + MvPolynomial.eval ![D, 1] bLip) r (φ := φ η) (f := F i) h1 h2
    rw [show D + MvPolynomial.eval ![D, 1] bLip = MvPolynomial.eval ![D, r] dD
        from (hdD D r).symm, hb2 D r] at h3
    exact h3
  -- the `1`-Lipschitz case for each pulled-back family
  choose Psi hPsi using fun η : Fin m =>
    hD3spec (MvPolynomial.eval ![D, r] b2) r k ε hε0 hε1 Λ
      (fun i l t => F i l (φ η l t)) (hGΩ η)
      (fun i l hl x hx => hI i l hl (φ η l x) (hφin η l hl x hx))
      (fun i l hl => hφlip η i l hl)
  -- the composed charts
  let Charts : Finset ((Fin p → ℝ) → ℝ → ℝ) :=
    (Finset.univ : Finset (Fin m)).biUnion
      (fun η => (Psi η).image (fun χ => fun l t => φ η l (χ l t)))
  -- the count bound
  have hPsi_le : ∀ η : Fin m, ((Psi η).card : ℝ) ≤
      MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] c3' := by
    intro η
    have h := (hPsi η).1
    rw [hc3' D r k (-Real.log ε)] at h
    exact h
  have hm_le : (m : ℝ) ≤ MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] c1 := by
    have h := hm
    rw [hc1 D r k (-Real.log ε)] at h
    exact h
  have hcard_le : Charts.card ≤
      ∑ η ∈ (Finset.univ : Finset (Fin m)), (Psi η).card := by
    have h1 := Work.WilG4a.card_biUnion_le (Finset.univ : Finset (Fin m))
      (fun η : Fin m => (Psi η).image (fun χ => fun l t => φ η l (χ l t)))
    have h2 : (∑ η ∈ (Finset.univ : Finset (Fin m)),
          ((Psi η).image (fun χ => fun l t => φ η l (χ l t))).card)
        ≤ ∑ η ∈ (Finset.univ : Finset (Fin m)), (Psi η).card :=
      Finset.sum_le_sum (fun η _ => Finset.card_image_le)
    exact le_trans h1 h2
  have hcard_bound : (Charts.card : ℝ) ≤
      (m : ℝ) * MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] c3' := by
    calc (Charts.card : ℝ)
        ≤ ((∑ η ∈ (Finset.univ : Finset (Fin m)), (Psi η).card : ℕ) : ℝ) := by
          exact_mod_cast hcard_le
      _ = ∑ η ∈ (Finset.univ : Finset (Fin m)),
            ((Psi η).card : ℝ) := by rw [Nat.cast_sum]
      _ ≤ ∑ _η ∈ (Finset.univ : Finset (Fin m)),
            MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] c3' :=
          Finset.sum_le_sum (fun η _ => hPsi_le η)
      _ = (m : ℝ) * MvPolynomial.eval
            ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] c3' := by
          simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hmax : (Charts.card : ℝ) ≤
      max (MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] (c1 * c3')) 0 := by
    refine le_trans hcard_bound ?_
    rw [le_max_iff]
    by_cases hB : 0 ≤ MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] c3'
    · exact Or.inl (by
        rw [map_mul]
        exact mul_le_mul_of_nonneg_right hm_le hB)
    · exact Or.inr (mul_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg m)
        (le_of_lt (not_le.mp hB)))
  have hfinal : (Charts.card : ℝ) ≤
      MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε]
        (c1 * c3' + (c1 * c3') * (c1 * c3') + 1) := by
    have heval : MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε]
        (c1 * c3' + (c1 * c3') * (c1 * c3') + 1)
        = MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] (c1 * c3')
          + MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] (c1 * c3')
            * MvPolynomial.eval ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] (c1 * c3')
          + 1 := by
      simp only [MvPolynomial.eval_add, MvPolynomial.eval_mul, map_one]
      try ring
    rw [heval]
    refine le_trans hmax ?_
    rw [max_le_iff]
    constructor
    · nlinarith [sq_nonneg (MvPolynomial.eval
        ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] (c1 * c3'))]
    · nlinarith [sq_nonneg (MvPolynomial.eval
        ![(D : ℝ), (r : ℝ), (k : ℝ), -Real.log ε] (c1 * c3') + 1 / 2)]
  refine ⟨Charts, hfinal, ?_, ?_⟩
  · -- per-chart conditions
    intro ψ hψ
    rw [Finset.mem_biUnion] at hψ
    obtain ⟨η, -, hψ⟩ := hψ
    rw [Finset.mem_image] at hψ
    obtain ⟨χ, hχ, rfl⟩ := hψ
    obtain ⟨-, hχOK, -⟩ := hPsi η
    -- Ω-definability of the composed chart, via the pullback rule
    have hχgraph : Work.WilG4a.graphFam χ ∈
        S.Ω a3 (MvPolynomial.eval ![D, r] b3') (p + 1 + 1) := by
      have h := (hχOK χ hχ).1
      rwa [hb3' D r] at h
    have hφgraph' : Work.WilG4a.graphFam (φ η) ∈
        S.Ω aLip (MvPolynomial.eval ![D, r] d1) (p + 1 + 1) := by
      have h := hφgraph η
      rwa [hd1 D r] at h
    have h1 : Work.WilG4a.graphFam χ ∈ S.Ω (max a3 aLip)
        (MvPolynomial.eval ![D, r] b3' + MvPolynomial.eval ![D, r] d1) (p + 1 + 1) :=
      Work.WilG5.mem_mono hχgraph _ _ (le_max_left _ _) (by omega)
    have h2 : Work.WilG4a.graphFam (φ η) ∈ S.Ω (max a3 aLip)
        (MvPolynomial.eval ![D, r] b3' + MvPolynomial.eval ![D, r] d1) (p + 1 + 1) :=
      Work.WilG5.mem_mono hφgraph' _ _ (le_max_right _ _) (by omega)
    have h3 := hPBSpec2 (MvPolynomial.eval ![D, r] b3' + MvPolynomial.eval ![D, r] d1) r
      (φ := χ) (f := φ η) h1 h2
    have hdeg : MvPolynomial.eval ![MvPolynomial.eval ![D, r] b3' +
        MvPolynomial.eval ![D, r] d1, r] b4 = MvPolynomial.eval ![D, r] b4' := by
      rw [show MvPolynomial.eval ![D, r] b3' + MvPolynomial.eval ![D, r] d1
          = MvPolynomial.eval ![D, r] (b3' + d1) from (MvPolynomial.eval_add ..).symm,
        hb4' D r]
    refine ⟨?_, ?_⟩
    · rwa [hdeg] at h3
    · intro l hl
      refine ⟨?_, ?_⟩
      · intro t ht
        exact hφin η l hl (χ l t) (((hχOK χ hχ).2 l hl).1 t ht)
      · intro i
        exact ((hχOK χ hχ).2 l hl).2 i
  · -- the ε-cover
    intro l hl x hx
    obtain ⟨η, t', ht', hφx⟩ := hφcov l hl x hx
    obtain ⟨-, -, hcov⟩ := hPsi η
    obtain ⟨χ, hχ, t, ht, hbound⟩ := hcov l hl t' ht'
    refine ⟨fun l t => φ η l (χ l t), ?_, t, ht, ?_⟩
    · exact Finset.mem_biUnion.mpr ⟨η, Finset.mem_univ η,
        Finset.mem_image.mpr ⟨χ, hχ, rfl⟩⟩
    · intro i
      have hb := hbound i
      have h1 : (fun i l t => F i l (φ η l t)) i l t' = F i l x := by
        show F i l (φ η l t') = F i l x
        rw [hφx]
      rw [h1] at hb
      simpa using hb

/-! ## The `1`-Lipschitz case -/

/-- `α + β · t` lies in the open unit interval when `0 ≤ α`, `0 < β`, `α + β ≤ 1` and
`t ∈ I`. -/
theorem affine_mem_I {α β t : ℝ} (hβ : 0 < β) (hα : 0 ≤ α) (hαβ : α + β ≤ 1)
    (ht : t ∈ I) : α + β * t ∈ I := by
  obtain ⟨ht0, ht1⟩ := ht
  constructor <;> nlinarith

/-- A function that is `C^1` on `I` with derivative bounded by `1` in absolute value is
`1`-Lipschitz on `I` (mean value inequality on the convex interval `I`). -/
theorem lip_of_deriv_le_one {g : ℝ → ℝ} (hg : ContDiffOn ℝ 1 g I)
    (hb : ∀ t ∈ I, |iteratedDeriv 1 g t| ≤ 1) :
    ∀ a ∈ I, ∀ b ∈ I, |g b - g a| ≤ |b - a| := by
  intro a ha b hbI
  have hdiff : ∀ x ∈ I, DifferentiableAt ℝ g x := by
    intro x hx
    exact (hg.differentiableOn_one x hx).differentiableAt (isOpen_Ioo.mem_nhds hx)
  have hbound : ∀ x ∈ I, ‖deriv g x‖ ≤ (1 : ℝ) := by
    intro x hx
    simpa [Real.norm_eq_abs, iteratedDeriv_one] using hb x hx
  have h := Convex.norm_image_sub_le_of_norm_deriv_le (f := g) (s := I) (C := 1) hdiff hbound
    (convex_Ioo (0 : ℝ) 1) (x := a) (y := b) ha hbI
  simpa [Real.norm_eq_abs] using h

/-- **The `1`-Lipschitz case of the `n = 1` family lemma.**  When every member of the family is
`C^1` on `I` with derivative bounded by `1`, BNZ Cor. 5.5 (`hFA`) already produces the charts:
they `ε`-cover the domain, `1`-Lipschitzness upgrades this to an `ε`-cover of the image, their
graphs are `Ω`-definable by `hAC`, and the derivative bounds are part of `hFA`'s conclusion. -/
theorem lip_case_flem1 (S : WilkiesDesign.SOMin)
    (hFA : ∀ p : ℕ, Work.WilG4a.F1Affine1 S p)
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
  -- BNZ Cor. 5.5 for this family, and `Ω`-definability of the resulting affine graphs
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
        exact affine_mem_I (hrest l hl).1 (hrest l hl).2.1 (hrest l hl).2.2.1 ht
      · intro i
        exact (hrest l hl).2.2.2 i
  · -- the `ε`-cover of the image
    intro l hl x hx
    obtain ⟨αβ, hαβ, t, ht, hlt⟩ := hcov0 l hl x hx
    obtain ⟨-, -, hrest⟩ := hprop0 αβ hαβ
    have hβl : 0 < αβ.2 l := (hrest l hl).1
    have hαl : 0 ≤ αβ.1 l := (hrest l hl).2.1
    have hsum : αβ.1 l + αβ.2 l ≤ 1 := (hrest l hl).2.2.1
    have hu : αβ.1 l + αβ.2 l * t ∈ I := affine_mem_I hβl hαl hsum ht
    refine ⟨fun l t => αβ.1 l + αβ.2 l * t, ?_, t, ht, ?_⟩
    · exact Finset.mem_image.mpr ⟨αβ, hαβ, rfl⟩
    · intro i
      have hg := hLipF i l hl
      have hlip := lip_of_deriv_le_one hg.1 hg.2 x hx (αβ.1 l + αβ.2 l * t) hu
      linarith

theorem fleem1_of_parts (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv) (hLip : ∀ (p F0 : ℕ), ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ) (cc : MvPolynomial (Fin 3) ℝ), ∀ (D k : ℕ) (Λ : Set (Fin p → ℝ)) (F : Fin k → (Fin p → ℝ) → ℝ → ℝ), (∀ i, Work.WilG4a.graphFam (F i) ∈ S.Ω F0 D (p + 1 + 1)) → (∀ i, ∀ l ∈ Λ, ∀ x ∈ Work.WilG4a.I, F i l x ∈ Work.WilG4a.I) → ∃ (m : ℕ), (m : ℝ) ≤ MvPolynomial.eval ![(D : ℝ), (1 : ℝ), (k : ℝ)] cc ∧ ∃ (φ : Fin m → (Fin p → ℝ) → ℝ → ℝ), (∀ η, Work.WilG4a.graphFam (φ η) ∈ S.Ω a (MvPolynomial.eval ![D, 1] b) (p + 1 + 1)) ∧ (∀ η l, l ∈ Λ → ∀ t ∈ Work.WilG4a.I, φ η l t ∈ Work.WilG4a.I) ∧ (∀ η (i : Fin k) (l : Fin p → ℝ), l ∈ Λ → ContDiffOn ℝ 1 (fun t : ℝ => F i l (φ η l t)) Work.WilG4a.I ∧ ∀ t ∈ Work.WilG4a.I, |iteratedDeriv 1 (fun t : ℝ => F i l (φ η l t)) t| ≤ 1) ∧ (∀ l ∈ Λ, ∀ x ∈ Work.WilG4a.I, ∃ η, ∃ t ∈ Work.WilG4a.I, φ η l t = x)) (hPB : ∀ (p F : ℕ), ∃ (a : ℕ) (b : MvPolynomial (Fin 2) ℕ), ∀ (D r : ℕ) {φ f : (Fin p → ℝ) → ℝ → ℝ}, Work.WilG4a.graphFam φ ∈ S.Ω F D (p + 1 + 1) → Work.WilG4a.graphFam f ∈ S.Ω F D (p + 1 + 1) → Work.WilG4a.graphFam (fun l t => f l (φ l t)) ∈ S.Ω a (MvPolynomial.eval ![D, r] b) (p + 1 + 1)) (hFA : ∀ p : ℕ, Work.WilG4a.F1Affine1 S p) (p : ℕ) : Work.WilG4a.FLem1 S p :=
  -- `fleem1_of_parts_of_lip` is the assembly; the `1`-Lipschitz case `lip_case_flem1` uses
  -- BNZ Cor. 5.5 (`hFA`) and the `Ω`-definability of affine charts (`affineChart_graph_mem`).
  fleem1_of_parts_of_lip S hLip hPB
    (fun (p : ℕ) (F0 : ℕ) => lip_case_flem1 S hFA (affineChart_graph_mem S) p F0) p

end Work.WilG4a
