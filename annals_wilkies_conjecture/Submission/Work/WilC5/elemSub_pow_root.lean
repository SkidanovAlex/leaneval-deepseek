import Mathlib
import Submission.Work.WilC5.ElemChain

/-!
  WilC5 — `elemSub_pow_root`.

  Every element `d` of an `LRc`-elementary substructure `S ≤ M` has an `n`-th root of its square
  *inside* `S`, provided such roots exist in `M` (hypothesis `hb`).

  The argument is pure elementarity, with no model-theoretic hypothesis on `M` itself.  For a fixed
  `n ≥ 1` the set `{y : M | y ^ n = d ^ 2}` is defined by the `LRc`-formula
  `∃ y, y ^ n = x ^ 2` evaluated at the parameter `d ∈ S`; by `hb` it is nonempty in `M`, so by
  elementarity of `S` (Tarski–Vaught: an elementary substructure realises every existential
  formula with parameters in `S` that `M` realises) it has a witness in `S`.

  The formula `y ^ n = x ^ 2` is built in the language of rings as a term power and transported to
  `LRc = (ring ⊕ rexpL)[[ℝ]]` along the two inclusions `ring → ring ⊑ rexpL → LRc`.
-/

set_option autoImplicit false

namespace Work.WilC5

open FirstOrder FirstOrder.Language

/-- The `n`-fold product of a ring term with itself (`n`-th power of a term). -/
private def powTerm {α : Type*} : Language.ring.Term α → ℕ → Language.ring.Term α
  | _, 0 => 1
  | t, k + 1 => powTerm t k * t

private lemma realize_powTerm {α : Type*} {R : Type*} [Monoid R] [Add R] [Neg R] [Zero R]
    [Ring.CompatibleRing R] (v : α → R) (t : Language.ring.Term α) (n : ℕ) :
    Term.realize v (powTerm t n) = (Term.realize v t) ^ n := by
  induction n with
  | zero => simp [powTerm, Ring.realize_one]
  | succ k ih => rw [powTerm, Ring.realize_mul, ih, pow_succ]

/-- The free variable `x` of the formula `y ^ n = x ^ 2`. -/
private def xT : Language.ring.Term (Fin 1 ⊕ Fin 1) := Term.var (Sum.inl 0)
/-- The variable `y` of the formula `y ^ n = x ^ 2`. -/
private def yT : Language.ring.Term (Fin 1 ⊕ Fin 1) := Term.var (Sum.inr 0)

/-- The ring-language formula `y ^ n = x ^ 2`, with `x` on the left of the sum and `y` on the
right. -/
private def psiRing (n : ℕ) : Language.ring.Formula (Fin 1 ⊕ Fin 1) :=
  Term.equal (powTerm yT n) (powTerm xT 2)

/-- Realization of `psiRing`: the second variable is the `n`-th power of the first. -/
private lemma psiRing_realize {R : Type*} [Monoid R] [Add R] [Neg R] [Zero R]
    [Ring.CompatibleRing R] (n : ℕ) (w i : Fin 1 → R) :
    (psiRing n).Realize (Sum.elim w i) ↔ (i 0) ^ n = (w 0) ^ 2 := by
  simp only [psiRing, Formula.realize_equal, realize_powTerm, yT, xT, Term.realize_var,
    Sum.elim_inr, Sum.elim_inl]

/-- `psiRing` transported into `LRc = (ring ⊕ rexpL)[[ℝ]]`. -/
private def psiRingLRc (n : ℕ) : WilkiesDesign.CG.LRc.Formula (Fin 1 ⊕ Fin 1) :=
  (lhomWithConstants (Language.ring.sum WilkiesDesign.CG.rexpL) ℝ).onFormula
    ((LHom.sumInl : Language.ring →ᴸ Language.ring.sum WilkiesDesign.CG.rexpL).onFormula
      (psiRing n))

/-- Realization of `psiRingLRc` in a model of the `LRc`-setting: the ring operations of `LRc`
interpret as the field operations. -/
private lemma psiRingLRc_realize {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [FirstOrder.Ring.CompatibleRing M] [WilkiesDesign.CG.rexpL.Structure M]
    [(FirstOrder.Language.constantsOn ℝ).Structure M]
    (n : ℕ) (w i : Fin 1 → M) :
    (psiRingLRc n).Realize (Sum.elim w i) ↔ (i 0) ^ n = (w 0) ^ 2 := by
  rw [psiRingLRc, LHom.realize_onFormula, LHom.realize_onFormula]
  exact psiRing_realize n w i

/-- The `LRc`-formula `∃ y, y ^ n = x ^ 2`, with the single free variable `x`. -/
private noncomputable def Phi (n : ℕ) : WilkiesDesign.CG.LRc.Formula (Fin 1) :=
  (psiRingLRc n).iExs

/-- Realization of `Phi`: `x` is a value whose square has an `n`-th root. -/
private lemma Phi_realize {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [FirstOrder.Ring.CompatibleRing M] [WilkiesDesign.CG.rexpL.Structure M]
    [(FirstOrder.Language.constantsOn ℝ).Structure M]
    (n : ℕ) (w : Fin 1 → M) :
    (Phi n).Realize w ↔ ∃ a : M, a ^ n = (w 0) ^ 2 := by
  rw [Phi, Formula.realize_iExs]
  constructor
  · rintro ⟨i, hi⟩
    rw [psiRingLRc_realize] at hi
    exact ⟨i 0, hi⟩
  · rintro ⟨a, ha⟩
    refine ⟨fun _ => a, ?_⟩
    rw [psiRingLRc_realize]
    simpa using ha

theorem elemSub_pow_root {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    [FirstOrder.Ring.CompatibleRing M] [WilkiesDesign.CG.rexpL.Structure M]
    [(FirstOrder.Language.constantsOn ℝ).Structure M]
    (S : WilkiesDesign.CG.LRc.ElementarySubstructure M)
    (hb : ∀ (b : M) (n : ℕ), 1 ≤ n → ∃ z : M, z ^ n = b ^ 2)
    {d : M} (hdS : d ∈ (S : Set M)) {n : ℕ} (hn : 1 ≤ n) :
    ∃ e ∈ (S : Set M), e ^ n = d ^ 2 := by
  let x : Fin 1 → S := fun _ => ⟨d, hdS⟩
  -- In `M`, the square of `d` has an `n`-th root by hypothesis.
  have hM : (Phi n).Realize ((S.subtype : S → M) ∘ x) := by
    rw [Phi_realize]
    obtain ⟨z, hz⟩ := hb d n hn
    exact ⟨z, by simpa [x] using hz⟩
  -- By elementarity the same existential holds in `S`, giving a witness `e : S`.
  have hS : (Phi n).Realize x := (S.subtype.map_formula (Phi n) x).mp hM
  rw [Phi, Formula.realize_iExs] at hS
  obtain ⟨e, he⟩ := hS
  -- Transport the witnessing equation from `S` back to `M`.
  have hfun : (Sum.elim ((S.subtype : S → M) ∘ x) ((S.subtype : S → M) ∘ e))
      = ((S.subtype : S → M) ∘ Sum.elim x e) := by
    funext t; rcases t with a | b <;> rfl
  have he' : (psiRingLRc n).Realize
      (Sum.elim ((S.subtype : S → M) ∘ x) ((S.subtype : S → M) ∘ e)) := by
    rw [hfun]
    exact (S.subtype.map_formula (psiRingLRc n) (Sum.elim x e)).mpr he
  rw [psiRingLRc_realize] at he'
  exact ⟨(e 0 : M), (e 0).2, by simpa [x] using he'⟩

end Work.WilC5
