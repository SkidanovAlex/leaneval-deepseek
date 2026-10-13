import Mathlib
import Submission.Work.WilC4.Defs
import Submission.Work.WilC4.SupDefs
import Submission.Work.WilC2.definable_fin_params
import Submission.Work.WilC2.Square

set_option autoImplicit false
set_option maxHeartbeats 1000000

noncomputable section
open Classical
namespace Work.WilC4

open FirstOrder FirstOrder.Language
open WilkiesDesign WilkiesDesign.CG
open Work.WilC2 (ParamFormula leF liftR liftR_realize leF_realize leF_realize_le
  exists_fin_relabel_elim model_exists_sq real_exists_sq)

/-- The logical content of the sup-existence formula for an abstract predicate `P`. -/
lemma exists_forall_iff_isLUB' {M : Type} [LinearOrder M] (P : M → Prop) (s : M) :
    (∀ q : Fin 2 → M, ∃ t : Fin 1 → M,
      ((P (q 0) → q 0 ≤ s) ∧ ((P (t 0) → t 0 ≤ q 1) → s ≤ q 1)))
      ↔ IsLUB {x | P x} s := by
  rw [isLUB_iff_le_iff]
  constructor
  · intro h b
    constructor
    · intro hs x hx
      obtain ⟨t, h1, _⟩ := h ![x, b]
      exact le_trans (h1 hx) hs
    · intro hb
      obtain ⟨t, _, h2⟩ := h ![b, b]
      exact h2 (fun ht => hb ht)
  · intro h q
    have hup : ∀ x, P x → x ≤ s := (h s).mp le_rfl
    have hex : ∃ t : Fin 1 → M, ((P (t 0) → t 0 ≤ q 1) → s ≤ q 1) := by
      by_cases hq : ∀ x, P x → x ≤ q 1
      · exact ⟨fun _ => q 0, fun _ => (h (q 1)).mpr hq⟩
      · have hex' : ∃ x, P x ∧ ¬ x ≤ q 1 := by
          by_contra hc
          apply hq
          intro x hx
          by_contra hxq
          exact hc ⟨x, hx, hxq⟩
        obtain ⟨x, hx, hxq⟩ := hex'
        exact ⟨fun _ => x, fun hc => absurd (hc hx) hxq⟩
    obtain ⟨t, ht⟩ := hex
    exact ⟨t, hup (q 0), ht⟩

/-! ## Semantics of the sup formulas

Everything in this section is uniform in an ordered field `M` whose nonnegative elements are
squares (`hsq`), which identifies the order of `M` with the order definable in the language
(`leF` is `∃ z, x + z * z = y`). -/

section Semantics

variable {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
  [Ring.CompatibleRing M] [rexpL.Structure M] [(constantsOn ℝ).Structure M]

/-- The fibre of the parametric formula `φ` over the parameter tuple `p`. -/
def fibre {n : ℕ} (φ : ParamFormula n) (p : Fin n → M) : Set M :=
  {x | φ.Realize (Sum.elim p (fun _ => x))}

/-- The realisation of the renamed formula `φ(t)`. -/
lemma phiVar_realize {n : ℕ} (φ : ParamFormula n) (t : SVar n) (w : SVar n → M) :
    (phiVar φ t).Realize w ↔ φ.Realize (Sum.elim (fun i => w (SVar.param i)) (fun _ => w t)) := by
  have hcomp : w ∘ (Sum.elim (fun i => SVar.param i) (fun _ : Fin 1 => t)) =
      Sum.elim (fun i => w (SVar.param i)) (fun _ => w t) := by
    funext a
    rcases a with i | k <;> rfl
  constructor
  · intro h
    rw [phiVar, Formula.realize_relabel, hcomp] at h
    exact h
  · intro h
    rw [phiVar, Formula.realize_relabel, hcomp]
    exact h

/-- The realisation of the order formula `a ≤ b`. -/
lemma leVar_realize {n : ℕ} (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z)
    (a b : SVar n) (w : SVar n → M) : (leVar a b).Realize w ↔ w a ≤ w b := by
  have h : w ∘ ![a, b] = ![w a, w b] := by
    funext i
    fin_cases i <;> rfl
  constructor
  · intro hh
    rw [leVar, liftR_realize, h] at hh
    exact (leF_realize_le hsq (w a) (w b)).mp hh
  · intro hh
    rw [leVar, liftR_realize, h]
    exact (leF_realize_le hsq (w a) (w b)).mpr hh

/-- The realisation of the "nonempty and bounded above" body, evaluated on the assignment
produced by the quantifier blocks. -/
lemma bodyP_realize' {n : ℕ} (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z)
    (φ : ParamFormula n) (p : Fin n → M) (z : Fin 1 → M) (q : Fin 2 → M) (t : Fin 1 → M) :
    (bodyP φ).Realize (rawV (default : Empty → M) p z q t) ↔
      φ.Realize (Sum.elim p (fun _ => q 0)) ∧
        (φ.Realize (Sum.elim p (fun _ => t 0)) → t 0 ≤ q 1) := by
  constructor
  · intro h
    simp only [bodyP, Formula.realize_inf, Formula.realize_imp, phiVar_realize,
      leVar_realize hsq, rawV_param, rawV_qu, rawV_wV] at h
    exact h
  · intro h
    simp only [bodyP, Formula.realize_inf, Formula.realize_imp, phiVar_realize,
      leVar_realize hsq, rawV_param, rawV_qu, rawV_wV]
    exact h

/-- The realisation of the "`z` is a least upper bound" body. -/
lemma bodyC_realize' {n : ℕ} (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z)
    (φ : ParamFormula n) (p : Fin n → M) (z : Fin 1 → M) (q : Fin 2 → M) (t : Fin 1 → M) :
    (bodyC φ).Realize (rawV (default : Empty → M) p z q t) ↔
      ((φ.Realize (Sum.elim p (fun _ => q 0)) → q 0 ≤ z 0) ∧
        ((φ.Realize (Sum.elim p (fun _ => t 0)) → t 0 ≤ q 1) → z 0 ≤ q 1)) := by
  constructor
  · intro h
    simp only [bodyC, Formula.realize_inf, Formula.realize_imp, phiVar_realize,
      leVar_realize hsq, rawV_param, rawV_qu, rawV_wV, rawV_zVar] at h
    exact h
  · intro h
    simp only [bodyC, Formula.realize_inf, Formula.realize_imp, phiVar_realize,
      leVar_realize hsq, rawV_param, rawV_qu, rawV_wV, rawV_zVar]
    exact h

/-- The realisation of `premiseF`, with the assignment produced by the quantifier blocks. -/
lemma premiseF_realize {n : ℕ} (φ : ParamFormula n) (p : Fin n → M) (z : Fin 1 → M) :
    (premiseF φ).Realize (Sum.elim (Sum.elim (default : Empty → M) p) z) ↔
      ∃ q : Fin 2 → M, ∀ t : Fin 1 → M,
        (bodyP φ).Realize (rawV (default : Empty → M) p z q t) := by
  constructor
  · intro h
    simp only [premiseF, Formula.realize_iExs, Formula.realize_iAlls] at h
    exact h
  · intro h
    simp only [premiseF, Formula.realize_iExs, Formula.realize_iAlls]
    exact h

/-- The realisation of `supF`, with the assignment produced by the quantifier blocks. -/
lemma supF_realize {n : ℕ} (φ : ParamFormula n) (p : Fin n → M) (z : Fin 1 → M) :
    (supF φ).Realize (Sum.elim (Sum.elim (default : Empty → M) p) z) ↔
      ∀ q : Fin 2 → M, ∃ t : Fin 1 → M,
        (bodyC φ).Realize (rawV (default : Empty → M) p z q t) := by
  constructor
  · intro h
    simp only [supF, Formula.realize_iAlls, Formula.realize_iExs] at h
    exact h
  · intro h
    simp only [supF, Formula.realize_iAlls, Formula.realize_iExs]
    exact h

/-- `premiseF` says that the fibre is nonempty and bounded above. -/
lemma premiseF_iff {n : ℕ} (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z)
    (φ : ParamFormula n) (p : Fin n → M) (z : Fin 1 → M) :
    (premiseF φ).Realize (Sum.elim (Sum.elim (default : Empty → M) p) z) ↔
      (∃ x : M, x ∈ fibre φ p) ∧ (∃ u : M, ∀ x : M, x ∈ fibre φ p → x ≤ u) := by
  rw [premiseF_realize]
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨⟨q 0, ?_⟩, ⟨q 1, fun y hy => ?_⟩⟩
    · exact ((bodyP_realize' hsq φ p z q (fun _ => 0)).mp (hq _)).1
    · exact ((bodyP_realize' hsq φ p z q (fun _ => y)).mp (hq _)).2 hy
  · rintro ⟨⟨x, hx⟩, ⟨u, hu⟩⟩
    refine ⟨![x, u], fun t => ?_⟩
    rw [bodyP_realize' hsq]
    exact ⟨hx, fun h => hu (t 0) h⟩

/-- `supF` says that `z 0` is the least upper bound of the fibre. -/
lemma supF_iff {n : ℕ} (hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z)
    (φ : ParamFormula n) (p : Fin n → M) (z : Fin 1 → M) :
    (supF φ).Realize (Sum.elim (Sum.elim (default : Empty → M) p) z) ↔
      IsLUB (fibre φ p) (z 0) := by
  rw [supF_realize]
  have h : (∀ q : Fin 2 → M, ∃ t : Fin 1 → M,
        (bodyC φ).Realize (rawV (default : Empty → M) p z q t)) ↔
      (∀ q : Fin 2 → M, ∃ t : Fin 1 → M,
        ((φ.Realize (Sum.elim p (fun _ => q 0)) → q 0 ≤ z 0) ∧
          ((φ.Realize (Sum.elim p (fun _ => t 0)) → t 0 ≤ q 1) → z 0 ≤ q 1))) := by
    refine forall_congr' (fun q => ?_)
    exact exists_congr (fun t => bodyC_realize' hsq φ p z q t)
  rw [h]
  exact exists_forall_iff_isLUB' (fun x => φ.Realize (Sum.elim p (fun _ => x))) (z 0)

end Semantics

/-- **The sup-existence sentence holds in `ℝ`** (completeness of `ℝ`). -/
theorem real_supSent {n : ℕ} (φ : ParamFormula n) : ℝ ⊨ supSent φ := by
  simp only [Sentence.Realize, supSent, Formula.realize_iAlls, Formula.realize_iExs,
    Formula.realize_imp]
  intro p
  by_cases hne : (fibre φ p).Nonempty
  · by_cases hbd : BddAbove (fibre φ p)
    · exact ⟨fun _ => sSup (fibre φ p), fun _ =>
        (supF_iff real_exists_sq φ p (fun _ => sSup (fibre φ p))).mpr
          (isLUB_csSup hne hbd)⟩
    · refine ⟨fun _ => 0, fun hprem => absurd ?_ hbd⟩
      exact ((premiseF_iff real_exists_sq φ p (fun _ => 0)).mp hprem).2
  · refine ⟨fun _ => 0, fun hprem => absurd ?_ hne⟩
    exact ((premiseF_iff real_exists_sq φ p (fun _ => 0)).mp hprem).1

/-- **The sup-existence sentence holds in every model of `TR`** (transfer). -/
theorem model_supSent {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [Ring.CompatibleRing M] [rexpL.Structure M] [(constantsOn ℝ).Structure M]
    (hM : M ⊨ TR) {n : ℕ} (φ : ParamFormula n) : M ⊨ supSent φ := by
  haveI : M ⊨ LRc.completeTheory ℝ := hM
  exact (realize_iff_of_model_completeTheory (L := LRc) (M := ℝ) (N := M)
    (supSent φ)).mpr (real_supSent φ)

theorem sup_exists_dcl {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M] [FirstOrder.Ring.CompatibleRing M] [WilkiesDesign.CG.rexpL.Structure M] [(FirstOrder.Language.constantsOn ℝ).Structure M] (hM : M ⊨ WilkiesDesign.CG.TR) {T : Set M} {X : Set M} (hX : T.Definable₁ WilkiesDesign.CG.LRc X) (hne : X.Nonempty) (hbdd : ∃ u : M, ∀ a ∈ X, a ≤ u) : ∃ s : M, IsLUB X s ∧ DefinableElt T ∅ s := by
  classical
  -- 1. extract a finite parameter set and a formula
  rw [Set.Definable₁] at hX
  obtain ⟨A0, hA0sub, hA0def⟩ := Set.definable_iff_finitely_definable.mp hX
  obtain ⟨φ, hφ⟩ := Set.definable_iff_exists_formula_sum.mp hA0def
  obtain ⟨n, σ, ψ, hψ⟩ := exists_fin_relabel_elim (L := LRc) (M := M) (k := 1) φ
  let p : Fin n → M := fun i => (σ i : M)
  have hmem : ∀ i, p i ∈ T := fun i => hA0sub (σ i).2
  -- 2. the fibre of `ψ` over `p` is `X`
  have hXeq : X = fibre ψ p := by
    have hfib : ∀ y : M, y ∈ fibre ψ p ↔ y ∈ X := by
      intro y
      have h1 : y ∈ X ↔ φ.Realize
          (Sum.elim (fun a : ↥(A0 : Set M) => (a : M)) (fun _ : Fin 1 => y)) := by
        have hh := Set.ext_iff.mp hφ (fun _ : Fin 1 => y)
        simpa using hh
      have h2 : ψ.Realize (Sum.elim p (fun _ : Fin 1 => y)) ↔ φ.Realize
          (Sum.elim (fun a : ↥(A0 : Set M) => (a : M)) (fun _ : Fin 1 => y)) :=
        hψ (fun a : ↥(A0 : Set M) => (a : M)) (fun _ : Fin 1 => y)
      rw [h1, ← h2]
      rfl
    exact Set.ext fun y => (hfib y).symm
  -- 3. transfer of the sup-existence sentence
  have hsq : ∀ x : M, 0 ≤ x → ∃ z : M, x = z * z := model_exists_sq hM
  have hS := model_supSent hM ψ
  simp only [Sentence.Realize, supSent, Formula.realize_iAlls, Formula.realize_iExs,
    Formula.realize_imp] at hS
  obtain ⟨z, hz⟩ := hS p
  have hprem : (premiseF ψ).Realize (Sum.elim (Sum.elim (default : Empty → M) p) z) := by
    rw [premiseF_iff hsq]
    refine ⟨?_, ?_⟩
    · obtain ⟨y, hy⟩ := hne
      exact ⟨y, by rw [← hXeq]; exact hy⟩
    · obtain ⟨u, hu⟩ := hbdd
      exact ⟨u, fun y hy => hu y (by rw [hXeq]; exact hy)⟩
  have hL : IsLUB (fibre ψ p) (z 0) := (supF_iff hsq ψ p z).mp (hz hprem)
  have hLX : IsLUB X (z 0) := hXeq.symm ▸ hL
  refine ⟨z 0, hLX, ?_⟩
  -- 4. definability: `z 0` is the unique point at which `supF ψ` holds
  have hkey : ∀ v : Fin 1 → M,
      (supF ψ).Realize (Sum.elim (Sum.elim (default : Empty → M) p) v) ↔ v 0 = z 0 := by
    intro v
    rw [supF_iff hsq ψ p v]
    constructor
    · intro hv
      have hvX : IsLUB X (v 0) := by
        rw [← hXeq] at hv
        exact hv
      exact (IsLUB.unique hLX hvX).symm
    · intro hv
      rw [hv]
      exact hL
  show (T ∪ ∅).Definable LRc {fun _ : Fin 1 => z 0}
  rw [Set.definable_iff_exists_formula_sum]
  let g : (Empty ⊕ Fin n) ⊕ Fin 1 → ↥(T ∪ ∅) ⊕ Fin 1 :=
    Sum.elim (Sum.elim (fun e : Empty => Empty.elim e)
      (fun i => Sum.inl (⟨p i, Set.mem_union_left ∅ (hmem i)⟩ : ↥(T ∪ ∅))))
      (fun k => Sum.inr k)
  refine ⟨(supF ψ).relabel g, ?_⟩
  ext v
  rw [Set.mem_singleton_iff, Set.mem_setOf_eq, Formula.realize_relabel]
  have hcomp : (Sum.elim (fun a : ↥(T ∪ ∅) => (a : M)) v) ∘ g =
      Sum.elim (Sum.elim (default : Empty → M) p) v := by
    funext a
    rcases a with (e | i) | k
    · exact Empty.elim e
    · rfl
    · rfl
  rw [hcomp, hkey v]
  constructor
  · intro hv
    rw [hv]
  · intro hv
    funext k
    show v k = z 0
    rw [show k = 0 from Subsingleton.elim k 0, hv]

end Work.WilC4
