/-
  WilC5 -- `Work.WilC5.StepExpDclExtend`.

  Let `K, L` be models of `TR = Th(ℝ_rexp, r)_{r ∈ ℝ}` in the language `LRc`, let `F ≤ K` be a
  `Dcl`-closed `LRc`-substructure of `K` (so `F ⊨ TR`), let `σ : F ↪ L` be an `LRc`-embedding,
  and let `x ∈ K`, `y ∈ L` cut the same gap through `σ`:
  `(f : K) < x ↔ σ f < y` and `x < (f : K) ↔ y < σ f` for all `f ∈ F`.

  Then `σ` extends to an `LRc`-embedding of the substructure `S ≤ K` with carrier exactly the
  definable closure `Dcl (F ∪ {x})`, sending `x` to `y`.

  Proof outline.

  * `A0 := (F : Set K) ∪ {x}` and `f₀ : ↥A0 → L` is `σ` on `F` and `y` at `x`.
    `cut_determines_type_F` (o-minimality of the models of `TR`, plus model completeness to make
    `σ` elementary) says that `x` and `y` have the same type over `F`; substituting a variable for
    the parameter `x` (`cut_transfer_on_insert`) upgrades this to: `f₀` preserves the realisation
    of *every* `LRc`-formula over the parameter set `A0` -- i.e. `f₀` is elementary on `A0`.
  * Every `z ∈ Dcl A0` is the unique solution of an `A0`-definable formula `Φ z`
    (`defFormula_of_dcl`); elementarity transfers the unique solvability to `L`, which yields the
    extension `g : ↥(Dcl A0) → L` of `f₀` (`dclExtend_elementarity`), elementary over the
    parameters `A0`, together with the characterising equation `g z = (the unique solution in L)`.
  * `Dcl A0` is `Dcl`-closed (`Work.WilC2.dcl_idem`), hence is the carrier of a substructure
    `S ≤ K` (`dclClosed_substructure`), with `F ≤ S` and `x ∈ S`.
  * Injectivity and preservation of the function symbols of `LRc` for `g` are immediate
    instances of the elementarity of `g` applied to the formulas `v = w` and `fn(v̄) = w`
    (`realize_eq_var`, `realize_eq_func`); `LRc` has no relation symbols.  This gives the
    embedding `σ' : S ↪ L`, which agrees with `σ` on `F` and sends `x` to `y` by construction.
-/
import Mathlib
import Submission.Work.WilC5.dmm42_cut_extend
import Submission.Work.WilC5.dclClosed_substructure
import Submission.Work.WilC5.model_TR_of_dcl_closed
import Submission.Work.WilC2.Dcl

set_option autoImplicit false
set_option maxHeartbeats 4000000
noncomputable section
open Classical FirstOrder FirstOrder.Language
open WilkiesDesign.CG

namespace Work.WilC5

/-! ## 1. Evaluating the test formulas -/

/-! ## helper lemmas for evaluating the test formulas -/

private lemma realize_eq_var {M α : Type} [LRc.Structure M] (u : α → M) (i j : α) :
    (((Term.var i).equal (Term.var j)) : LRc.Formula α).Realize u ↔ u i = u j := by
  rw [Formula.realize_equal, Term.realize_var, Term.realize_var]

private lemma realize_eq_func {M α : Type} [LRc.Structure M] {n : ℕ}
    (fn : LRc.Functions n) (u : α → M) (i : α) (k : Fin n → α) :
    (((Term.func fn (fun j => Term.var (k j))).equal (Term.var i)) :
        LRc.Formula α).Realize u ↔ Structure.funMap fn (fun j => u (k j)) = u i := by
  rw [Formula.realize_equal, Term.realize_func]
  simp only [Term.realize_var]


/-! ## 2. A defining formula for every point of the definable closure -/

/-- Every point of `Dcl A` is the unique solution of an `A`-definable `LRc`-formula. -/
private theorem defFormula_of_dcl {K : Type} [FirstOrder.Language.Structure WilkiesDesign.CG.LRc K]
    (A : Set K) :
    ∃ Φ : ((z : ↥(Work.WilC2.Dcl A)) → WilkiesDesign.CG.LRc.Formula (↥A ⊕ Fin 1)),
      ∀ (z : ↥(Work.WilC2.Dcl A)) (w : Fin 1 → K),
        w 0 = (z : K) ↔ (Φ z).Realize (Sum.elim Subtype.val w) := by
  have key : ∀ z : ↥(Work.WilC2.Dcl A), ∃ φ : WilkiesDesign.CG.LRc.Formula (↥A ⊕ Fin 1),
      ∀ w : Fin 1 → K, w 0 = (z : K) ↔ φ.Realize (Sum.elim Subtype.val w) := by
    intro z
    have hz : A.Definable₁ WilkiesDesign.CG.LRc ({(z : K)} : Set K) := z.2
    rw [Set.Definable₁] at hz
    rw [Set.definable_iff_exists_formula_sum] at hz
    obtain ⟨φ, hφ⟩ := hz
    exact ⟨φ, fun w => by
      have h := Set.ext_iff.mp hφ w
      simpa [Set.mem_setOf_eq, Set.mem_singleton_iff] using h⟩
  exact ⟨fun z => Classical.choose (key z), fun z => Classical.choose_spec (key z)⟩


private theorem cut_transfer_on_insert {K L : Type}
    [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FirstOrder.Ring.CompatibleRing K]
    [WilkiesDesign.CG.rexpL.Structure K] [(FirstOrder.Language.constantsOn ℝ).Structure K]
    [FirstOrder.Language.Theory.Model K WilkiesDesign.CG.TR]
    [Field L] [LinearOrder L] [IsStrictOrderedRing L] [FirstOrder.Ring.CompatibleRing L]
    [WilkiesDesign.CG.rexpL.Structure L] [(FirstOrder.Language.constantsOn ℝ).Structure L]
    [FirstOrder.Language.Theory.Model L WilkiesDesign.CG.TR]
    (hMCr : WilkiesDesign.CG.ModelComplete WilkiesDesign.CG.TR)
    (hOM : WilkiesDesign.CG.OMinModels)
    (F : WilkiesDesign.CG.LRc.Substructure K)
    (hF : FirstOrder.Language.Theory.Model (F : Type) WilkiesDesign.CG.TR)
    (hFdcl : Work.WilC2.Dcl (F : Set K) ⊆ (F : Set K))
    (σ : WilkiesDesign.CG.LRc.Embedding F L) {x : K} {y : L}
    (hcut : (∀ f : F, ((f : K) < x ↔ (σ f : L) < y)) ∧
      (∀ f : F, (x < (f : K) ↔ y < (σ f : L))))
    (f0 : ↥((F : Set K) ∪ {x}) → L)
    (hf0 : ∀ a : ↥((F : Set K) ∪ {x}),
      ((h : (a : K) ∈ (F : Set K)) → f0 a = σ ⟨a.1, h⟩) ∧
      ((a : K) ∉ (F : Set K) → f0 a = y)) :
    ∀ (θ : WilkiesDesign.CG.LRc.Formula ↥((F : Set K) ∪ {x})),
      θ.Realize (Subtype.val : ↥((F : Set K) ∪ {x}) → K) ↔ θ.Realize f0 := by
  classical
  intro θ
  let s : ↥((F : Set K) ∪ {x}) → WilkiesDesign.CG.LRc.Term (F ⊕ Fin 1) := fun a =>
    if h : (a : K) ∈ (F : Set K) then Term.var (Sum.inl ⟨a.1, h⟩) else Term.var (Sum.inr 0)
  set W0 : F ⊕ Fin 1 → K := Sum.elim Subtype.val (fun _ : Fin 1 => x) with hW0
  set W1 : F ⊕ Fin 1 → L := Sum.elim (fun f : F => (σ f : L)) (fun _ : Fin 1 => y) with hW1
  have hKW : ∀ (v : Fin 0 → F),
      (Sum.elim Subtype.val (Fin.cons x (fun i => (v i : K)))) = W0 := by
    intro v
    funext c
    rcases c with f | k
    · rfl
    · fin_cases k
      rfl
  have hLW : ∀ (v : Fin 0 → F),
      (Sum.elim (fun f : F => (σ f : L)) (Fin.cons y (fun i => (σ (v i) : L)))) = W1 := by
    intro v
    funext c
    rcases c with f | k
    · rfl
    · fin_cases k
      rfl
  have hcut' := Work.WilC5.cut_determines_type_F hMCr hOM F hF hFdcl σ hcut
    (φ := θ.subst s) (v := fun i : Fin 0 => i.elim0)
  rw [hKW (fun i : Fin 0 => i.elim0), hLW (fun i : Fin 0 => i.elim0)] at hcut'
  have hsubst0 : (fun a : ↥((F : Set K) ∪ {x}) => (s a).realize W0) =
      (Subtype.val : ↥((F : Set K) ∪ {x}) → K) := by
    funext a
    by_cases h : (a : K) ∈ (F : Set K)
    · have hs : s a = Term.var (Sum.inl (⟨a.1, h⟩ : F)) := dif_pos h
      rw [hs, Term.realize_var, hW0]
      rfl
    · have hs : s a = Term.var (Sum.inr (0 : Fin 1)) := dif_neg h
      rw [hs, Term.realize_var, hW0]
      simp only [Sum.elim_inr]
      have hx : x = (a : K) := by
        rcases a.2 with h' | h'
        · exact absurd h' h
        · exact (Set.mem_singleton_iff.mp h').symm
      exact hx
  have hsubst1 : (fun a : ↥((F : Set K) ∪ {x}) => (s a).realize W1) = f0 := by
    funext a
    by_cases h : (a : K) ∈ (F : Set K)
    · have hs : s a = Term.var (Sum.inl (⟨a.1, h⟩ : F)) := dif_pos h
      rw [hs, Term.realize_var, hW1]
      simp only [Sum.elim_inl]
      exact ((hf0 a).1 h).symm
    · have hs : s a = Term.var (Sum.inr (0 : Fin 1)) := dif_neg h
      rw [hs, Term.realize_var, hW1]
      simp only [Sum.elim_inr]
      exact ((hf0 a).2 h).symm
  have hsubstK : Formula.Realize (θ.subst s) W0 ↔
      Formula.Realize θ (fun a => (s a).realize W0) := by
    simp only [Formula.Realize, BoundedFormula.realize_subst]
  have hsubstL : Formula.Realize (θ.subst s) W1 ↔
      Formula.Realize θ (fun a => (s a).realize W1) := by
    simp only [Formula.Realize, BoundedFormula.realize_subst]
  have h0 : Formula.Realize (θ.subst s) W0 ↔
      Formula.Realize θ (Subtype.val : ↥((F : Set K) ∪ {x}) → K) := by
    rw [hsubstK, hsubst0]
  have h1 : Formula.Realize (θ.subst s) W1 ↔ Formula.Realize θ f0 := by
    rw [hsubstL, hsubst1]
  exact h0.symm.trans (hcut'.trans h1)

private theorem dclExtend_elementarity {K L : Type} [FirstOrder.Language.Structure WilkiesDesign.CG.LRc K]
    [FirstOrder.Language.Structure WilkiesDesign.CG.LRc L]
    (A : Set K) (f : ↥A → L)
    (hf : ∀ (θ : WilkiesDesign.CG.LRc.Formula ↥A),
      θ.Realize (Subtype.val : ↥A → K) ↔ θ.Realize f)
    (Φ : (z : ↥(Work.WilC2.Dcl A)) → WilkiesDesign.CG.LRc.Formula (↥A ⊕ Fin 1))
    (hΦ : ∀ (z : ↥(Work.WilC2.Dcl A)) (w : Fin 1 → K),
        w 0 = (z : K) ↔ (Φ z).Realize (Sum.elim Subtype.val w)) :
    ∃ g : ↥(Work.WilC2.Dcl A) → L,
      (∀ (a : ↥A) (h : (a : K) ∈ Work.WilC2.Dcl A), g ⟨a.1, h⟩ = f a) ∧
      (∀ {n : ℕ} (θ : WilkiesDesign.CG.LRc.Formula (↥A ⊕ Fin n))
        (v : Fin n → ↥(Work.WilC2.Dcl A)),
        θ.Realize (Sum.elim Subtype.val (fun j => (v j : K))) ↔
        θ.Realize (Sum.elim f (fun j => g (v j)))) := by
  classical
  have huniqK : ∀ z : ↥(Work.WilC2.Dcl A),
      ∃! i : Fin 1 → K, (Φ z).Realize (Sum.elim Subtype.val i) := by
    intro z
    refine ⟨fun _ => (z : K), (hΦ z (fun _ => (z : K))).mp rfl, ?_⟩
    intro i hi
    funext k
    rw [Subsingleton.elim k 0]
    exact (hΦ z i).mpr hi
  have huniqL : ∀ z : ↥(Work.WilC2.Dcl A),
      ∃! i : Fin 1 → L, (Φ z).Realize (Sum.elim f i) := by
    intro z
    exact (Formula.realize_iExsUnique (φ := Φ z) (v := f)).mp
      ((hf _).mp ((Formula.realize_iExsUnique (φ := Φ z)
        (v := (Subtype.val : ↥A → K))).mpr (huniqK z)))
  let g : ↥(Work.WilC2.Dcl A) → L := fun z => (huniqL z).choose 0
  have gspec : ∀ z : ↥(Work.WilC2.Dcl A),
      (Φ z).Realize (Sum.elim f (fun _ : Fin 1 => g z)) := by
    intro z
    have heq : (fun _ : Fin 1 => g z) = (huniqL z).choose := by
      funext k
      show g z = (huniqL z).choose k
      rw [Subsingleton.elim k 0]
    rw [heq]
    exact (huniqL z).choose_spec.1
  have guniq : ∀ (z : ↥(Work.WilC2.Dcl A)) (w : L),
      (Φ z).Realize (Sum.elim f (fun _ : Fin 1 => w)) → w = g z := by
    intro z w hw
    have h2 := (huniqL z).choose_spec.2 (fun _ : Fin 1 => w) hw
    have h3 := congr_fun h2 0
    simpa [g] using h3
  have hmain : ∀ {n : ℕ} (θ : WilkiesDesign.CG.LRc.Formula (↥A ⊕ Fin n))
      (v : Fin n → ↥(Work.WilC2.Dcl A)),
      θ.Realize (Sum.elim Subtype.val (fun j => (v j : K))) ↔
      θ.Realize (Sum.elim f (fun j => g (v j))) := by
    intro n θ v
    let ψ : WilkiesDesign.CG.LRc.Formula (↥A ⊕ Fin n) :=
      (Formula.iInf (fun j : Fin n =>
        (Φ (v j)).relabel (Sum.map id (fun _ : Fin 1 => j)))) ⊓ θ
    have hψK : ∀ u : Fin n → K, ψ.Realize (Sum.elim Subtype.val u) ↔
        (∀ j : Fin n, u j = (v j : K)) ∧ θ.Realize (Sum.elim Subtype.val u) := by
      intro u
      have hψdef : ψ = (Formula.iInf (fun j : Fin n =>
          (Φ (v j)).relabel (Sum.map id (fun _ : Fin 1 => j)))) ⊓ θ := rfl
      rw [hψdef, Formula.realize_inf, Formula.realize_iInf]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨fun j => ?_, h2⟩
        have hj := h1 j
        rw [Formula.realize_relabel] at hj
        have hcomp : ((Sum.elim (Subtype.val : ↥A → K) u) ∘ (Sum.map id (fun _ : Fin 1 => j))) =
            Sum.elim (Subtype.val : ↥A → K) (fun _ : Fin 1 => u j) := by
          funext c
          rcases c with a | k <;> rfl
        rw [hcomp] at hj
        exact (hΦ (v j) (fun _ : Fin 1 => u j)).mpr hj
      · rintro ⟨h1, h2⟩
        refine ⟨fun j => ?_, h2⟩
        rw [Formula.realize_relabel]
        have hcomp : ((Sum.elim (Subtype.val : ↥A → K) u) ∘ (Sum.map id (fun _ : Fin 1 => j))) =
            Sum.elim (Subtype.val : ↥A → K) (fun _ : Fin 1 => u j) := by
          funext c
          rcases c with a | k <;> rfl
        rw [hcomp]
        exact (hΦ (v j) (fun _ : Fin 1 => u j)).mp (h1 j)
    have hψL : ∀ u : Fin n → L, ψ.Realize (Sum.elim f u) ↔
        (∀ j : Fin n, u j = g (v j)) ∧ θ.Realize (Sum.elim f u) := by
      intro u
      have hψdef : ψ = (Formula.iInf (fun j : Fin n =>
          (Φ (v j)).relabel (Sum.map id (fun _ : Fin 1 => j)))) ⊓ θ := rfl
      rw [hψdef, Formula.realize_inf, Formula.realize_iInf]
      constructor
      · rintro ⟨h1, h2⟩
        refine ⟨fun j => ?_, h2⟩
        have hj := h1 j
        rw [Formula.realize_relabel] at hj
        have hcomp : ((Sum.elim (f : ↥A → L) u) ∘ (Sum.map id (fun _ : Fin 1 => j))) =
            Sum.elim (f : ↥A → L) (fun _ : Fin 1 => u j) := by
          funext c
          rcases c with a | k <;> rfl
        rw [hcomp] at hj
        exact guniq (v j) (u j) hj
      · rintro ⟨h1, h2⟩
        refine ⟨fun j => ?_, h2⟩
        rw [Formula.realize_relabel]
        have hcomp : ((Sum.elim (f : ↥A → L) u) ∘ (Sum.map id (fun _ : Fin 1 => j))) =
            Sum.elim (f : ↥A → L) (fun _ : Fin 1 => u j) := by
          funext c
          rcases c with a | k <;> rfl
        rw [hcomp]
        rw [h1 j]
        exact gspec (v j)
    have hχ : (Formula.iExs (Fin n) ψ).Realize (Subtype.val : ↥A → K) ↔
        (Formula.iExs (Fin n) ψ).Realize f := hf _
    rw [Formula.realize_iExs] at hχ
    rw [Formula.realize_iExs] at hχ
    have hK : (∃ i : Fin n → K, ψ.Realize (Sum.elim Subtype.val i)) ↔
        θ.Realize (Sum.elim Subtype.val (fun j => (v j : K))) := by
      constructor
      · rintro ⟨u, hu⟩
        rw [hψK u] at hu
        have hfun : u = (fun j => (v j : K)) := funext hu.1
        rw [← hfun]
        exact hu.2
      · intro h
        exact ⟨(fun j => (v j : K)), (hψK _).mpr ⟨fun j => rfl, h⟩⟩
    have hL : (∃ i : Fin n → L, ψ.Realize (Sum.elim f i)) ↔
        θ.Realize (Sum.elim f (fun j => g (v j))) := by
      constructor
      · rintro ⟨u, hu⟩
        rw [hψL u] at hu
        have hfun : u = (fun j => g (v j)) := funext hu.1
        rw [← hfun]
        exact hu.2
      · intro h
        exact ⟨(fun j => g (v j)), (hψL _).mpr ⟨fun j => rfl, h⟩⟩
    exact hK.symm.trans (hχ.trans hL)
  refine ⟨g, ?_, hmain⟩
  intro a h
  let v : Fin 1 → ↥(Work.WilC2.Dcl A) := fun _ => ⟨a.1, h⟩
  have key := hmain (θ := ((Term.var (Sum.inl a)).equal (Term.var (Sum.inr (0 : Fin 1))) :
      WilkiesDesign.CG.LRc.Formula (↥A ⊕ Fin 1))) (v := v)
  have hK : (((Term.var (Sum.inl a)).equal (Term.var (Sum.inr (0 : Fin 1))) :
      WilkiesDesign.CG.LRc.Formula (↥A ⊕ Fin 1))).Realize
      (Sum.elim Subtype.val (fun j => (v j : K))) := by
    rw [realize_eq_var]
    simp [v]
  have hR := key.mp hK
  rw [realize_eq_var] at hR
  simp only [Sum.elim_inl, Sum.elim_inr, v] at hR
  exact hR.symm

theorem StepExpDclExtend {K L : Type}
    [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FirstOrder.Ring.CompatibleRing K]
    [WilkiesDesign.CG.rexpL.Structure K] [(FirstOrder.Language.constantsOn ℝ).Structure K]
    [FirstOrder.Language.Theory.Model K WilkiesDesign.CG.TR]
    [Field L] [LinearOrder L] [IsStrictOrderedRing L] [FirstOrder.Ring.CompatibleRing L]
    [WilkiesDesign.CG.rexpL.Structure L] [(FirstOrder.Language.constantsOn ℝ).Structure L]
    [FirstOrder.Language.Theory.Model L WilkiesDesign.CG.TR]
    (hMCr : WilkiesDesign.CG.ModelComplete WilkiesDesign.CG.TR)
    (hOM : WilkiesDesign.CG.OMinModels)
    (F : WilkiesDesign.CG.LRc.Substructure K) (hF : FirstOrder.Language.Theory.Model (F : Type) WilkiesDesign.CG.TR)
    (hFdcl : Work.WilC2.Dcl (F : Set K) ⊆ (F : Set K))
    (σ : WilkiesDesign.CG.LRc.Embedding F L) {x : K} {y : L}
    (hcut : (∀ f : F, ((f : K) < x ↔ (σ f : L) < y)) ∧
      (∀ f : F, (x < (f : K) ↔ y < (σ f : L)))) :
    ∃ (S : WilkiesDesign.CG.LRc.Substructure K)
      (hS : (S : Set K) = Work.WilC2.Dcl ((F : Set K) ∪ {x}))
      (hSdcl : Work.WilC2.Dcl (S : Set K) ⊆ (S : Set K))
      (hle : F ≤ S) (hxS : x ∈ (S : Set K)),
      ∃ σ' : WilkiesDesign.CG.LRc.Embedding S L,
        (∀ f : F, σ' ⟨(f : K), hle f.2⟩ = σ f) ∧ σ' ⟨x, hxS⟩ = y := by
  classical
  let A0 : Set K := (F : Set K) ∪ {x}
  let f0 : ↥A0 → L := fun a => if h : (a : K) ∈ (F : Set K) then σ ⟨a.1, h⟩ else y
  have hf0 : ∀ a : ↥A0,
      ((h : (a : K) ∈ (F : Set K)) → f0 a = σ ⟨a.1, h⟩) ∧
      ((a : K) ∉ (F : Set K) → f0 a = y) := by
    intro a
    constructor
    · intro h; dsimp only [f0]; exact dif_pos h
    · intro h; dsimp only [f0]; exact dif_neg h
  -- the map `σ ∪ {(x,y)}` is elementary on `A0 = F ∪ {x}`
  have htrans : ∀ (θ : LRc.Formula ↥A0),
      θ.Realize (Subtype.val : ↥A0 → K) ↔ θ.Realize f0 :=
    cut_transfer_on_insert hMCr hOM F hF hFdcl σ hcut f0 hf0
  obtain ⟨Φ, hΦ⟩ := defFormula_of_dcl (K := K) A0
  obtain ⟨g, hg_ext, hg_tr⟩ := dclExtend_elementarity A0 f0 htrans Φ hΦ
  -- the `dcl`-closed substructure with carrier `Dcl A0`
  have hdclIdem : Work.WilC2.Dcl (Work.WilC2.Dcl A0) ⊆ Work.WilC2.Dcl A0 := by
    rw [Work.WilC2.dcl_idem A0]
  obtain ⟨S, hS⟩ := Work.WilC5.dclClosed_substructure (M := K)
    (A := Work.WilC2.Dcl A0) hdclIdem
  have hSdcl : Work.WilC2.Dcl (S : Set K) ⊆ (S : Set K) := by
    rw [hS]; exact hdclIdem
  have hA0dcl : A0 ⊆ Work.WilC2.Dcl A0 := fun a ha =>
    Work.WilC2.mem_dcl.mpr (Set.Definable.singleton_of_mem LRc ha)
  have hle : F ≤ S := by
    refine (SetLike.coe_subset_coe).mpr ?_
    intro a ha
    show a ∈ (S : Set K)
    rw [hS]
    exact hA0dcl (Or.inl ha)
  have hxS : x ∈ (S : Set K) := by
    rw [hS]
    exact hA0dcl (Or.inr (Set.mem_singleton x))
  -- the map on `↥S` induced by `g`
  let sf : ↥S → L := fun a => g ⟨a.1, hS ▸ a.2⟩
  -- consistency: if `x ∈ F` then `y = σ x`
  have hconsist : ∀ (h : x ∈ (F : Set K)), (σ ⟨x, h⟩ : L) = y := by
    intro h
    have h1 := hcut.1 ⟨x, h⟩
    have h2 := hcut.2 ⟨x, h⟩
    rcases lt_trichotomy (σ ⟨x, h⟩ : L) y with hlt | heq | hgt
    · exact absurd (h1.mpr hlt) (lt_irrefl x)
    · exact heq
    · exact absurd (h2.mpr hgt) (lt_irrefl x)
  have hsfF : ∀ f : F, sf ⟨(f : K), hle f.2⟩ = σ f := by
    intro f
    have h1 : g ⟨(f : K), hS ▸ hle f.2⟩ = f0 ⟨(f : K), Or.inl f.2⟩ :=
      hg_ext ⟨(f : K), Or.inl f.2⟩ (hS ▸ hle f.2)
    have h2 : f0 ⟨(f : K), Or.inl f.2⟩ = σ f := by
      have hh := (hf0 ⟨(f : K), Or.inl f.2⟩).1 f.2
      exact hh.trans (congrArg σ (Subtype.ext rfl))
    show sf ⟨(f : K), hle f.2⟩ = σ f
    exact h1.trans h2
  have hsfx : sf ⟨x, hxS⟩ = y := by
    have h1 : g ⟨x, hS ▸ hxS⟩ = f0 ⟨x, Or.inr (Set.mem_singleton x)⟩ :=
      hg_ext ⟨x, Or.inr (Set.mem_singleton x)⟩ (hS ▸ hxS)
    have h2 : f0 ⟨x, Or.inr (Set.mem_singleton x)⟩ = y := by
      by_cases hxF : x ∈ (F : Set K)
      · have hh := (hf0 ⟨x, Or.inr (Set.mem_singleton x)⟩).1 hxF
        exact hh.trans (hconsist hxF)
      · exact (hf0 ⟨x, Or.inr (Set.mem_singleton x)⟩).2 hxF
    show sf ⟨x, hxS⟩ = y
    exact h1.trans h2
  -- injectivity of `sf`
  have hinj : Function.Injective sf := by
    intro z w hzw
    let v : Fin 2 → ↥(Work.WilC2.Dcl A0) :=
      Fin.cons ⟨(z : K), hS ▸ z.2⟩ (Fin.cons ⟨(w : K), hS ▸ w.2⟩ (fun i : Fin 0 => i.elim0))
    have hv0 : v 0 = (⟨(z : K), hS ▸ z.2⟩ : ↥(Work.WilC2.Dcl A0)) := rfl
    have hv1 : v 1 = (⟨(w : K), hS ▸ w.2⟩ : ↥(Work.WilC2.Dcl A0)) := rfl
    have key := hg_tr
      (θ := ((Term.var (Sum.inr (0 : Fin 2))).equal (Term.var (Sum.inr (1 : Fin 2))) :
        LRc.Formula (↥A0 ⊕ Fin 2)))
      (v := v)
    have hRHS : (((Term.var (Sum.inr (0 : Fin 2))).equal
        (Term.var (Sum.inr (1 : Fin 2))) : LRc.Formula (↥A0 ⊕ Fin 2))).Realize
        (Sum.elim f0 (fun j => g (v j))) := by
      rw [realize_eq_var]
      simp only [Sum.elim_inr, hv0, hv1]
      show sf z = sf w
      exact hzw
    have hLHS := key.mpr hRHS
    rw [realize_eq_var] at hLHS
    simp only [Sum.elim_inr, hv0, hv1] at hLHS
    exact Subtype.ext hLHS
  -- preservation of function symbols
  have hfun : ∀ {n : ℕ} (fn : LRc.Functions n) (a : Fin n → ↥S),
      sf (Structure.funMap fn a) = Structure.funMap fn (sf ∘ a) := by
    intro n fn a
    let v : Fin (n + 1) → ↥(Work.WilC2.Dcl A0) :=
      Fin.snoc (fun i : Fin n => ⟨(a i : K), hS ▸ (a i).2⟩)
        ⟨Structure.funMap fn (fun i => (a i : K)),
          hS ▸ (S.fun_mem fn (fun i => (a i : K)) (fun i => (a i).2))⟩
    have hvcast : ∀ i : Fin n, v (Fin.castSucc i) = (⟨(a i : K), hS ▸ (a i).2⟩ : ↥(Work.WilC2.Dcl A0)) := by
      intro i
      dsimp only [v]
      exact Fin.snoc_castSucc _ _ i
    have hvlast : v (Fin.last n) = (⟨Structure.funMap fn (fun i => (a i : K)),
        hS ▸ (S.fun_mem fn (fun i => (a i : K)) (fun i => (a i).2))⟩ : ↥(Work.WilC2.Dcl A0)) := by
      dsimp only [v]
      exact Fin.snoc_last _ _
    have key := hg_tr
      (θ := ((Term.func fn (fun j : Fin n => Term.var (Sum.inr (Fin.castSucc j)))).equal
        (Term.var (Sum.inr (Fin.last n))) : LRc.Formula (↥A0 ⊕ Fin (n + 1))))
      (v := v)
    have hLHS : (((Term.func fn (fun j : Fin n => Term.var (Sum.inr (Fin.castSucc j)))).equal
        (Term.var (Sum.inr (Fin.last n))) : LRc.Formula (↥A0 ⊕ Fin (n + 1)))).Realize
        (Sum.elim Subtype.val (fun j => (v j : K))) := by
      rw [realize_eq_func]
      simp only [Sum.elim_inr]
      have h1 : (fun j : Fin n => (v (Fin.castSucc j) : K)) = (fun i => (a i : K)) := by
        funext j; rw [hvcast]
      rw [h1, hvlast]
    have hRHS := key.mp hLHS
    rw [realize_eq_func] at hRHS
    simp only [Sum.elim_inr] at hRHS
    rw [hvlast] at hRHS
    have hcast : (fun j : Fin n => g (v (Fin.castSucc j))) = (fun j => sf (a j)) := by
      funext j
      rw [hvcast]
    rw [hcast] at hRHS
    show sf (Structure.funMap fn a) = Structure.funMap fn (sf ∘ a)
    exact hRHS.symm
  have hrel : ∀ {n : ℕ} (r : LRc.Relations n) (a : Fin n → ↥S),
      Structure.RelMap r (sf ∘ a) ↔ Structure.RelMap r a :=
    fun {n : ℕ} r a => nomatch r
  refine ⟨S, hS, hSdcl, hle, hxS, ?_⟩
  refine ⟨{ toFun := sf, inj' := hinj, map_fun' := hfun, map_rel' := hrel }, ?_, ?_⟩
  · intro f
    exact hsfF f
  · exact hsfx


end Work.WilC5
