/-
  WilC6 — the "`M`-side compactness step" of the amalgamation argument for `transfer_of_isEF`.

  Given structures `M`, `N` of `LEc`, tuples `a : Fin n → M`, `b : Fin n → N` of the same
  *existential* type (`h`), and a *finite* family `F` of `IsEF` sentences of `LEc[[M]]` which
  hold in `M` with the constants interpreted by the identity, we produce a single function
  `χ : M → N` which maps `a i ↦ b i` and which realizes all the sentences of `F`.

  The proof: let `S ⊆ M ⊕ Empty` be the (finite) set of `M`-constants occurring in the
  sentences of `F`, and let `γ = {x // x ∈ S}`.  Relabel each sentence
  `constantsVarsEquiv ψ` (a formula with free variables in `M ⊕ Empty`) along the map `g`
  which sends a constant `m` to the variable `i` if `m = a i`, and to its own extra variable
  otherwise; conjoin the results over `ψ ∈ F` and existentially quantify the extra variables.
  The resulting formula `Ψ` (with free variables `Fin n`) is `IsEF`, so `h` transports its
  realization from `a` to `b`; the values of the extra variables in the witness in `N` then
  define `χ` on the constants of `S`, and the formula itself says that all the sentences of
  `F` hold.

  (The hypothesis `hb` is what makes `χ` well defined on the overlap of `S` with the image
  of `a`; the assertion that the tuple `a` is as injective as `b` is exactly the
  well-definedness of `a i ↦ b i`.)
-/
import Mathlib
import Submission.Work.WilC6.Base

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section

open Classical
open FirstOrder.Language
open WilkiesDesign WilkiesDesign.CG

namespace Work.WilC6.IsEF

/-! ### Syntactic closure properties of `IsEF`

`IsEF` is closed under relabelling of variables, under relabelling a formula (a special case),
under existentially quantifying a finite block of free variables, and under the "turn the
constants of `L[[γ]]` into free variables" map `constantsVarsEquiv`. -/

/-- `IsEF` is preserved by `BoundedFormula.relabel`. -/
theorem relabel_chi {L : FirstOrder.Language} {α β : Type*} {m k : ℕ}
    {φ : L.BoundedFormula α k} (h : Work.WilC6.IsEF φ) (g : α → β ⊕ Fin m) :
    Work.WilC6.IsEF (φ.relabel g) := by
  induction h with
  | top => exact Work.WilC6.IsEF.top
  | bot => exact Work.WilC6.IsEF.bot
  | bdEq t₁ t₂ => exact Work.WilC6.IsEF.bdEq _ _
  | bdNe t₁ t₂ => exact Work.WilC6.IsEF.bdNe _ _
  | inf _ _ ih₁ ih₂ => exact Work.WilC6.IsEF.inf ih₁ ih₂
  | sup _ _ ih₁ ih₂ => exact Work.WilC6.IsEF.sup ih₁ ih₂
  | ex _ ih => rw [BoundedFormula.relabel_ex]; exact Work.WilC6.IsEF.ex ih

/-- `IsEF` is preserved by `Formula.relabel` (relabelling the free variables of a formula). -/
theorem formulaRelabel_chi {L : FirstOrder.Language} {α β : Type*} {φ : L.Formula α}
    (h : Work.WilC6.IsEF φ) (g : α → β) : Work.WilC6.IsEF (Formula.relabel g φ) :=
  relabel_chi h (Sum.inl ∘ g)

/-- `IsEF` is preserved by `BoundedFormula.exs` (existentially quantifying all bound
variables). -/
theorem exs_chi {L : FirstOrder.Language} {α : Type*} :
    ∀ {n : ℕ} {ψ : L.BoundedFormula α n}, Work.WilC6.IsEF ψ → Work.WilC6.IsEF ψ.exs
  | 0, _, h => h
  | _n + 1, _, h => (h.ex).exs_chi

/-- `IsEF` is preserved by `Formula.iExs` (existentially quantifying a finite block of free
variables). -/
theorem iExs_chi {L : FirstOrder.Language} {α β : Type*} [Finite β] {φ : L.Formula (α ⊕ β)}
    (h : Work.WilC6.IsEF φ) : Work.WilC6.IsEF (Formula.iExs β φ) := by
  rw [Formula.iExs]
  exact (h.relabel_chi _).exs_chi

/-- `IsEF` is preserved by a simultaneous relabelling of terms and relations that does not
change the arities (`BoundedFormula.mapTermRel` with the trivial binder map). -/
theorem mapTermRel_chi {L L' : FirstOrder.Language} {α β : Type*}
    (ft : ∀ k, L.Term (α ⊕ Fin k) → L'.Term (β ⊕ Fin k))
    (fr : ∀ k, L.Relations k → L'.Relations k) {m : ℕ} {φ : L.BoundedFormula α m}
    (h : Work.WilC6.IsEF φ) :
    Work.WilC6.IsEF (BoundedFormula.mapTermRel (g := fun k => k) ft fr (fun _ => id) φ) := by
  induction h with
  | top => exact Work.WilC6.IsEF.top
  | bot => exact Work.WilC6.IsEF.bot
  | bdEq t₁ t₂ => exact Work.WilC6.IsEF.bdEq _ _
  | bdNe t₁ t₂ => exact Work.WilC6.IsEF.bdNe _ _
  | inf _ _ ih₁ ih₂ => exact Work.WilC6.IsEF.inf ih₁ ih₂
  | sup _ _ ih₁ ih₂ => exact Work.WilC6.IsEF.sup ih₁ ih₂
  | ex _ ih => exact Work.WilC6.IsEF.ex ih

/-- `IsEF` is preserved by turning the constants of `L[[γ]]` into free variables. -/
theorem constantsVars_chi {L : FirstOrder.Language} {γ : Type*} {n : ℕ}
    {φ : (FirstOrder.Language.withConstants L γ).BoundedFormula Empty n}
    (h : Work.WilC6.IsEF φ) :
    Work.WilC6.IsEF (BoundedFormula.constantsVarsEquiv φ) := by
  simp only [BoundedFormula.constantsVarsEquiv, BoundedFormula.mapTermRelEquiv_apply]
  exact mapTermRel_chi _ _ h

end Work.WilC6.IsEF

namespace Work.WilC6.Transfer

/-- Realization of a finite conjunction of formulas over a `Finset`. -/
theorem realize_finset_foldr {L : FirstOrder.Language} {ι α : Type*} {K : Type} [L.Structure K]
    (F : Finset ι) (f : ι → L.Formula α) (v : α → K) :
    Formula.Realize ((F.toList.map f).foldr (· ⊓ ·) ⊤) v ↔ ∀ i ∈ F, Formula.Realize (f i) v := by
  simp only [Formula.Realize, BoundedFormula.realize_foldr_inf]
  constructor
  · intro h i hi
    exact h (f i) (List.mem_map.mpr ⟨i, Finset.mem_toList.mpr hi, rfl⟩)
  · intro h φ hφ
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hφ
    exact h i (Finset.mem_toList.mp hi)

/-- Realization of a bounded formula depends only on the values at its free variables. -/
theorem realize_congr_freeVar_chi {L : FirstOrder.Language} {α : Type*} {n : ℕ} [DecidableEq α]
    {φ : L.BoundedFormula α n} {M : Type} [L.Structure M] {v₁ v₂ : α → M} {xs : Fin n → M}
    (h : ∀ a ∈ φ.freeVarFinset, v₁ a = v₂ a) : (φ.Realize v₁ xs ↔ φ.Realize v₂ xs) := by
  have hs : (↑φ.freeVarFinset : Set α) ⊆ ↑φ.freeVarFinset := le_refl _
  have h1 := BoundedFormula.realize_restrictFreeVar' (φ := φ) (v := v₁) (xs := xs) hs
  have h2 := BoundedFormula.realize_restrictFreeVar' (φ := φ) (v := v₂) (xs := xs) hs
  have hv : (v₁ ∘ ((↑) : ↑φ.freeVarFinset → α)) = (v₂ ∘ ((↑) : ↑φ.freeVarFinset → α)) := by
    funext a
    exact h a.1 a.2
  have hiff : ((φ.restrictFreeVar (Set.inclusion hs)).Realize
        (v₁ ∘ ((↑) : ↑φ.freeVarFinset → α)) xs)
      = ((φ.restrictFreeVar (Set.inclusion hs)).Realize
        (v₂ ∘ ((↑) : ↑φ.freeVarFinset → α)) xs) :=
    congrArg (fun w : ↑φ.freeVarFinset → M =>
      (φ.restrictFreeVar (Set.inclusion hs)).Realize w xs) hv
  have hiff' : ((φ.restrictFreeVar (Set.inclusion hs)).Realize
        (v₁ ∘ ((↑) : ↑φ.freeVarFinset → α)) xs)
      ↔ ((φ.restrictFreeVar (Set.inclusion hs)).Realize
        (v₂ ∘ ((↑) : ↑φ.freeVarFinset → α)) xs) :=
    ⟨fun hx => Eq.mp hiff hx, fun hx => Eq.mpr hiff hx⟩
  exact h1.symm.trans (hiff'.trans h2)

theorem exists_chi_of_isEF {n : ℕ} {M N : Type}
    [FirstOrder.Language.Structure WilkiesDesign.CG.LEc M]
    [FirstOrder.Language.Structure WilkiesDesign.CG.LEc N]
    (a : Fin n → M) (b : Fin n → N)
    (h : ∀ Ψ : FirstOrder.Language.Formula WilkiesDesign.CG.LEc (Fin n),
      Work.WilC6.IsEF Ψ → Ψ.Realize a → Ψ.Realize b)
    (hb : ∀ i j : Fin n, a i = a j → b i = b j)
    (F : Finset (FirstOrder.Language.Sentence (FirstOrder.Language.withConstants WilkiesDesign.CG.LEc M)))
    (hF : ∀ ψ ∈ F, Work.WilC6.IsEF ψ ∧
      FirstOrder.Language.Formula.Realize (FirstOrder.Language.BoundedFormula.constantsVarsEquiv ψ)
        (Sum.elim id (fun e : Empty => e.elim))) :
    ∃ χ : M → N, (∀ i, χ (a i) = b i) ∧
      ∀ ψ ∈ F,
        FirstOrder.Language.Formula.Realize (FirstOrder.Language.BoundedFormula.constantsVarsEquiv ψ)
          (Sum.elim χ (fun e : Empty => e.elim)) := by
  classical
  -- The finite set of `M`-constants occurring in the sentences of `F`.
  let S : Finset (M ⊕ Empty) :=
    F.biUnion fun ψ => (BoundedFormula.constantsVarsEquiv ψ).freeVarFinset
  -- The index type of the extra constants, together with one junk value.
  let γ : Type := {x : M ⊕ Empty // x ∈ S}
  haveI hγf : Fintype γ := Finset.fintypeCoeSort S
  haveI hγfin : Finite γ := Finite.of_fintype γ
  haveI hOfin : Finite (Option γ) := Finite.of_fintype (Option γ)
  -- Some element of `M`, used as a default value.
  let dM : M := Term.realize (fun e : Empty => e.elim)
    (Term.func (L := LEc) (Sum.inl (Sum.inl (FirstOrder.ringFunc.zero : FirstOrder.ringFunc 0)))
      (fun i : Fin 0 => i.elim0))
  -- Assignment of the extra constants in `M`: the identity on the support.
  let ρ : Option γ → M := fun y =>
    match y with
    | none => dM
    | some x => match x.1 with
      | Sum.inl m => m
      | Sum.inr e => nomatch e
  -- `g` sends a constant `m` to the variable `i` if `m = a i`, and to its own extra variable
  -- otherwise.
  let g : M ⊕ Empty → Fin n ⊕ Option γ := fun x =>
    match x with
    | Sum.inr e => nomatch e
    | Sum.inl m =>
      if hh : ∃ i : Fin n, a i = m then Sum.inl (Classical.choose hh)
      else Sum.inr (if hm : Sum.inl m ∈ S then some ⟨Sum.inl m, hm⟩ else none)
  -- The conjoined, relabelled sentences, with the extra variables free.
  let Ψ₀ : LEc.Formula (Fin n ⊕ Option γ) :=
    (F.toList.map fun ψ => Formula.relabel g (BoundedFormula.constantsVarsEquiv ψ)).foldr
      (· ⊓ ·) ⊤
  -- Existentially quantify the extra variables.
  let Ψ : LEc.Formula (Fin n) := Formula.iExs (Option γ) Ψ₀
  -- The two evaluation properties of `g`.
  have g_inl_pos : ∀ (m : M) (hh : ∃ i : Fin n, a i = m),
      g (Sum.inl m) = Sum.inl (Classical.choose hh) := by
    intro m hh
    simp only [g, dif_pos hh]
  have g_inl_neg : ∀ (m : M) (hh : ¬ ∃ i : Fin n, a i = m) (hm : Sum.inl m ∈ S),
      g (Sum.inl m) = Sum.inr (some ⟨Sum.inl m, hm⟩) := by
    intro m hh hm
    simp only [g, dif_neg hh, dif_pos hm]
  -- Realization of the conjunction, in `M` and in `N`.
  have hΨ₀_realizeM : ∀ v : Fin n ⊕ Option γ → M, Formula.Realize Ψ₀ v ↔
      ∀ ψ ∈ F, Formula.Realize (Formula.relabel g (BoundedFormula.constantsVarsEquiv ψ)) v := by
    intro v
    exact realize_finset_foldr F
      (fun ψ => Formula.relabel g (BoundedFormula.constantsVarsEquiv ψ)) v
  have hΨ₀_realizeN : ∀ v : Fin n ⊕ Option γ → N, Formula.Realize Ψ₀ v ↔
      ∀ ψ ∈ F, Formula.Realize (Formula.relabel g (BoundedFormula.constantsVarsEquiv ψ)) v := by
    intro v
    exact realize_finset_foldr F
      (fun ψ => Formula.relabel g (BoundedFormula.constantsVarsEquiv ψ)) v
  -- `Ψ₀` and `Ψ` are existential formulas.
  have hΨ₀_isEF : Work.WilC6.IsEF Ψ₀ := by
    show Work.WilC6.IsEF ((F.toList.map fun ψ =>
      Formula.relabel g (BoundedFormula.constantsVarsEquiv ψ)).foldr (· ⊓ ·) ⊤)
    apply Work.WilC6.IsEF.folds_inf
    intro φ hφ
    obtain ⟨ψ, hψ, rfl⟩ := List.mem_map.mp hφ
    exact Work.WilC6.IsEF.formulaRelabel_chi
      (Work.WilC6.IsEF.constantsVars_chi (hF ψ (Finset.mem_toList.mp hψ)).1) g
  have hΨ_isEF : Work.WilC6.IsEF Ψ := Work.WilC6.IsEF.iExs_chi hΨ₀_isEF
  -- `Ψ` holds at `a` in `M`.
  have hΨa : Formula.Realize Ψ a := by
    rw [show Ψ = Formula.iExs (Option γ) Ψ₀ from rfl, Formula.realize_iExs]
    refine ⟨ρ, ?_⟩
    rw [hΨ₀_realizeM (Sum.elim a ρ)]
    intro ψ hψF
    rw [Formula.realize_relabel]
    refine (realize_congr_freeVar_chi (φ := BoundedFormula.constantsVarsEquiv ψ)
      (v₁ := Sum.elim id (fun e : Empty => e.elim))
      (v₂ := (Sum.elim a ρ) ∘ g) ?_).1 (hF ψ hψF).2
    intro x hx
    rcases x with m | e
    · simp only [Function.comp_apply, Sum.elim_inl, id_eq]
      by_cases hh : ∃ i : Fin n, a i = m
      · rw [g_inl_pos m hh, Sum.elim_inl]
        exact (Classical.choose_spec hh).symm
      · have hm : Sum.inl m ∈ S := Finset.mem_biUnion.mpr ⟨ψ, hψF, hx⟩
        simp only [g_inl_neg m hh hm, Sum.elim_inr, ρ]
    · exact nomatch e
  -- Transport to `N` and extract the witness for the extra variables.
  have hΨb : Formula.Realize Ψ b := h Ψ hΨ_isEF hΨa
  rw [show Ψ = Formula.iExs (Option γ) Ψ₀ from rfl, Formula.realize_iExs] at hΨb
  obtain ⟨ν, hν⟩ := hΨb
  rw [hΨ₀_realizeN (Sum.elim b ν)] at hν
  -- The map `χ`, defined from `ν` and the assignment `g` of variables to constants.
  let χ : M → N := fun m => (Sum.elim b ν) (g (Sum.inl m))
  refine ⟨χ, ?_, ?_⟩
  · intro i
    show (Sum.elim b ν) (g (Sum.inl (a i))) = b i
    have hh : ∃ j : Fin n, a j = a i := ⟨i, rfl⟩
    rw [g_inl_pos (a i) hh, Sum.elim_inl]
    exact hb (Classical.choose hh) i (Classical.choose_spec hh)
  · intro ψ hψF
    have h1 := hν ψ hψF
    rw [Formula.realize_relabel] at h1
    have h2 : (Sum.elim χ (fun e : Empty => e.elim)) = (Sum.elim b ν) ∘ g := by
      funext x
      rcases x with m | e
      · simp only [Function.comp_apply, Sum.elim_inl]
        rfl
      · exact nomatch e
    rw [h2]
    exact h1

end Work.WilC6.Transfer
