import Submission.Work.Wilkies.Defs
import Submission.Work.WilkiesD.Truncation
import Submission.Work.WilkiesI.MemAlg
import Submission.Work.WilkiesB.Main
import Submission.Work.Wilkies.E.Spec
import Submission.Work.Wilkies.CG.Spec
import Submission.Work.Wilkies.CG.C4a.Spec
import Submission.Work.WilkiesH.H_count_proved

set_option autoImplicit false
noncomputable section
open Classical
namespace WilkiesDesign
open WilkiesConjecture

/-! ## Area statements (holes) -/

/-- **Area B (syntax, mechanical).** Flatten nested `exp` terms, push the Mathlib
`BoundedFormula` through ∧, ∨, ¬, ∃ and ∀. Complements are the hypothesis `hW`. -/
theorem B_syntax
    (hW : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), ExpExist X → ExpExist Xᶜ)
    {n : ℕ} (X : Set (Fin n → ℝ)) (h : IsRExpDefinable X) : ExpExist X :=
  WilkiesDesign.B_syntax_proved hW X h

/-- **Area E0 (Gabrielov's theorem of the complement for ℝ_rexp; proved inside E).** -/
theorem E0_rexp_complement {n : ℕ} (X : Set (Fin n → ℝ)) (h : RExpExist X) :
    RExpExist Xᶜ :=
  E.E0_from_parts X h

/-- **Area C (Wilkie: model completeness of ℝ_exp, RESEARCH).** It may use E0 (route C-R:
Ressayre / van den Dries–Macintyre–Marker transfer from ℝ_rexp). -/
theorem C_wilkie_complement
    (hR : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), RExpExist X → RExpExist Xᶜ)
    {n : ℕ} (X : Set (Fin n → ℝ)) (h : ExpExist X) : ExpExist Xᶜ :=
  CG.C_wilkie_complement_wiring hR CG.E0b_unif_finite
    (CG.C4a.C4a_wiring hR CG.E0b_unif_finite) X h

/-- **Area E (the restricted-exp sharply o-minimal structure, RESEARCH, largest).**
Binyamini–Vorobjov (+ Gabrielov–Vorobjov, Khovanskii) for sharp CD; BNZ §3 for sharp
derivatives. The truncated zero sets have format and degree that do NOT depend on `M`. -/
theorem E_instance : ∃ S : SOMin, S.SharpCD ∧ S.SharpDeriv ∧
    ∀ N d : ℕ, ∃ F D : ℕ, ∀ (M : ℝ) (P : MvPolynomial (Fin N ⊕ Fin N) ℝ),
      P.totalDegree ≤ d → boxZero M P ∈ S.Ω F D N :=
  E.E_instance_from_parts

/-- **Area G (BNZ algebraic lemma, §4–5).** -/
theorem G_alg_lemma (S : SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv) (F n : ℕ) :
    AlgLemma S F n :=
  CG.G_alg_lemma_wiring S hcd hder F n

/-- **Area I (local algebraic graph ⊆ X  ⇒  inside X.alg; mechanical).** The set `V` is a
Lean-semialgebraic set (in use, the zero set of polynomials). Inside the open box `W` around
`p`, it is the graph of a continuous section `ψ` of a coordinate projection of positive
rank, and it lies in `X`. -/
theorem I_mem_alg {n μ : ℕ} (hμ : 0 < μ) (X V : Set (Fin n → ℝ)) (hV : IsSemialgebraic V)
    (p : Fin n → ℝ) (δ : ℝ) (hδ : 0 < δ) (e : Fin μ ↪ Fin n)
    (U : Set (Fin μ → ℝ)) (hU : IsOpen U) (ψ : (Fin μ → ℝ) → (Fin n → ℝ))
    (hψ : ContinuousOn ψ U) (hsec : ∀ t ∈ U, ψ t ∘ e = t)
    (hgraph : V ∩ {x | ∀ i, |x i - p i| < δ} = ψ '' U)
    (hpV : p ∈ V) (hX : V ∩ {x | ∀ i, |x i - p i| < δ} ⊆ X) : p ∈ X.alg :=
  WilkiesDesign.I_mem_alg_proved hμ X V hV p δ hδ e U hU ψ hψ hsec hgraph hpV hX

/-- **Area H (point counting, BNZ §6; uses G and I).** -/
theorem H_count (S : SOMin) (hcd : S.SharpCD) (hder : S.SharpDeriv)
    (hG : ∀ F n : ℕ, AlgLemma S F n) (F n : ℕ) : CountBound S F n := by
  exact WilkiesDesign.H_count_proved S hcd hder hG F n  -- curric-46 lead 10-10: area H delivered

/-- **Area D (truncation + polynomial bookkeeping, mechanical).** BNZ's proof of Cor. 1:
for a finite `T` choose `M` covering witnesses, use `X_M ⊆ X ⇒ X_M.alg ⊆ X.alg`, push
`boxZero` through `m` projections, then substitute `D := D₀` into the 3-variable bound. -/
theorem D_truncation (S : SOMin)
    (hbox : ∀ N d : ℕ, ∃ F D : ℕ, ∀ (M : ℝ) (P : MvPolynomial (Fin N ⊕ Fin N) ℝ),
      P.totalDegree ≤ d → boxZero M P ∈ S.Ω F D N)
    (hcount : ∀ F n : ℕ, CountBound S F n)
    {n : ℕ} (X : Set (Fin n → ℝ)) (hX : ExpExist X) :
    ∃ f : MvPolynomial (Fin 2) ℝ, ∀ (g H : ℕ),
      Nat.card (degreeHeightLE X.trans g H) ≤ f.eval ![(g : ℝ), Real.log H] :=
  Work.WilkiesD.D_truncation_proved S hbox hcount X hX

/-! ## TOP wiring (complete modulo the holes above) -/

theorem corollary_1 {n : ℕ} (X : Set (Fin n → ℝ)) (h : IsRExpDefinable X) :
    ∃ f : MvPolynomial (Fin 2) ℝ, ∀ (g H : ℕ),
      Nat.card (degreeHeightLE X.trans g H) ≤ f.eval ![(g : ℝ), Real.log H] := by
  obtain ⟨S, hcd, hder, hbox⟩ := E_instance
  have hW : ∀ (n : ℕ) (X : Set (Fin n → ℝ)), ExpExist X → ExpExist Xᶜ :=
    fun n X hX => C_wilkie_complement (fun n Y hY => E0_rexp_complement Y hY) X hX
  exact D_truncation S hbox (H_count S hcd hder (G_alg_lemma S hcd hder)) X (B_syntax hW X h)

end WilkiesDesign
