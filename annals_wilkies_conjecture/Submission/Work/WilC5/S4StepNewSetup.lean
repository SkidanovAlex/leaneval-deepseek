/-
  WilC5 — **setup for vdDMM Lemma 4.4** (`S4StepNew`).

  The hard step of §4 of van den Dries–Macintyre–Marker builds, from an element `x ∉ F₀` in the
  fortified situation (their (4.1): `F₀` is `Dcl`-closed, log-closed, closed under exponentiation,
  and `v(F₀(y)^×) ≠ v(F₀^×)` for all `y ∉ F₀`), the sequence

  * `x₀ = x` (normalised), `log xₙ = βₙ + εₙ x_{n+1}`, `βₙ ∈ F₀`, `εₙ = ±1`,

  the tower of definable closures

  * `Fₙ = Dcl (F₀ ∪ {x₀, …, x_{n-1}})`,

  and, on the `L`-side, a sequence `yₙ` defined by `y_{n+1} = εₙ (log yₙ − σ βₙ)`, starting from a
  realisation `y₀` of the image of the cut of `x₀` under `σ`.  This module fixes the objects that
  all the remaining pieces of that lemma mention:

  * `Work.WilC5.CutReal σ x y` — "`y` realises the image under `σ` of the cut of `x`", the
    hypothesis under which `Work.WilC5.CutExtendsDcl` (the o-minimality input of vdDMM 4.2)
    extends `σ` to `Dcl (F ∪ {x})`;
  * `Work.WilC5.StepSeq.Fset S n` — the set `Fₙ`; `Work.WilC5.StepSeq.Fsub S n` — the same set as
    an `LRc`-substructure;
  * `Work.WilC5.StepSeq.ys B τ S y₀` — the `L`-side sequence, with `ys_rel` its defining relation.

  Nothing here is deep.  The only content is the transfer of `Work.WilC2.dcl_idem` to the
  `rexp`-reduct `Work.WilC5.reductStruct` at which the whole §4 layer is stated (`dcl_idem_reduct`,
  using `canonStruct`/`reductStruct_eq_withConstants` of `StepNoNewPrep`), and the bookkeeping of
  the two forms of `F_{n+1}`.
-/
import Mathlib
import Submission.Work.WilC5.StepSeq
import Submission.Work.WilC5.Values
import Submission.Work.WilC5.ValArith
import Submission.Work.WilC2.meetsDefinable_dcl

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
noncomputable section
open Classical
namespace Work.WilC5

open WilkiesDesign WilkiesDesign.CG WilkiesConjecture FirstOrder Language
open scoped FirstOrder

attribute [local instance] Work.WilC5.reductStruct

/-- **A realisation of a cut.**  `CutReal σ x y` says that `y` realises the image under `σ` of the
cut of `x`: for every parameter `a` of the domain, `a < x ↔ σ a < y` and `x < a ↔ y < σ a`
(vdDMM's "`y` realizes the image of the cut of `x`", the hypothesis of their Lemma 4.2). -/
def CutReal {K L : Type} [LEc.Structure K] [LEc.Structure L] [LinearOrder K] [LinearOrder L]
    {A : Set K} (σ : A → L) (x : K) (y : L) : Prop :=
  ∀ a : A, ((a : K) < x ↔ σ a < y) ∧ (x < (a : K) ↔ y < σ a)

/-- Cut realisation restricts to a smaller parameter set. -/
theorem CutReal.restrict {K L : Type} [LEc.Structure K] [LEc.Structure L] [LinearOrder K]
    [LinearOrder L] {A A' : Set K} {σ : A → L} {σ' : A' → L} {x : K} {y : L}
    (h : CutReal σ' x y) (hsub : A ⊆ A')
    (hag : ∀ (a : A) (ha : (a : K) ∈ A'), σ' ⟨(a : K), ha⟩ = σ a) :
    CutReal σ x y := by
  intro a
  obtain ⟨h1, h2⟩ := h ⟨(a : K), hsub a.2⟩
  rw [hag a (hsub a.2)] at h1 h2
  exact ⟨h1, h2⟩

/-- **The `LRc`-structure synthesized from the ordered-field instances**, i.e. the structure
`LR.withConstantsStructure ℝ` whose ring part is `Ring.CompatibleRing.toStructure`.  This is the
structure at which the `WilC2`/`WilC4` `Dcl`- and cut-API (`Work.WilC2.Dcl`,
`Work.WilC5.realizes_cut`, `Work.WilC5.DclExtension`, `Work.WilC5.leEL_iff_le`, …) is stated, and
which is *not* definitionally the `rexp`-reduct `Work.WilC5.reductStruct` at which the §4 layer
lives.  The alignment of the two is the explicit hypothesis `hstr` of the transport lemmas. -/
def canonField (K : Type) [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    [FirstOrder.Ring.CompatibleRing K] [rexpL.Structure K]
    [(FirstOrder.Language.constantsOn ℝ).Structure K] : LRc.Structure K :=
  @Language.withConstantsStructure LR K
    (@Language.sumStructure Language.ring rexpL K
      (FirstOrder.Ring.CompatibleRing.toStructure (self := (inferInstance : FirstOrder.Ring.CompatibleRing K)))
      (inferInstance : rexpL.Structure K))
    ℝ (inferInstance : (FirstOrder.Language.constantsOn ℝ).Structure K)

namespace StepSeq

variable {K : Type} [LEc.Structure K] {B : LRc.Substructure K}

/-! ## 1. `Dcl` at the `rexp`-reduct: containment and idempotence -/

/-- Every set is contained in its definable closure. -/
theorem subset_dcl {A : Set K} : A ⊆ @Work.WilC2.Dcl K (reductStruct K) A :=
  fun x hx => Work.WilC2.mem_dcl.mpr (Set.Definable.singleton_of_mem LRc hx)

/-- **The syntactic `LRc`-structure of a canonical instance bundle is the `rexp`-reduct.**
(With the canonical ordered-field data on `K`, `LR.withConstantsStructure ℝ` unfolds to the same
term as `reductStruct K`; this is the explicit equality with which the `WilC2`/`WilC4` `Dcl`-API
crosses between the two.) -/
theorem canonStruct_eq_reduct :
    (reductStruct K : LRc.Structure K) = LR.withConstantsStructure ℝ := by
  ext n f y
  · rcases f with (g | c)
    · rcases g with (g | r)
      · rfl
      · cases r; show rexpFromExp (y 0) = _; rfl
    · rfl
  · nomatch f

/-- **Idempotence of the definable closure** at the `rexp`-reduct (transported from
`Work.WilC2.dcl_idem`). -/
theorem dcl_idem_reduct (hK : K ⊨ TE) (A : Set K) :
    @Work.WilC2.Dcl K (reductStruct K) (@Work.WilC2.Dcl K (reductStruct K) A)
      = @Work.WilC2.Dcl K (reductStruct K) A := by
  have hKTR : @Theory.Model LRc K (reductStruct K) TR := reduct_model_TR K hK
  letI : Field K := cField K hK
  letI : LinearOrder K := cLin K hK
  letI : IsStrictOrderedRing K := tr_isStrictOrderedRing K hKTR
  haveI : K ⊨ Theory.field := tr_ring_field K hKTR
  letI : FirstOrder.Ring.CompatibleRing K := FirstOrder.Field.compatibleRingOfModelField K
  have hstruct : (reductStruct K : LRc.Structure K) = LR.withConstantsStructure ℝ :=
    canonStruct_eq_reduct (K := K)
  rw [hstruct]
  exact Work.WilC2.dcl_idem (M := K) A

/-- `Dcl (Dcl X ∪ Y) = Dcl (X ∪ Y)`: adjoining parameters that are already definable is harmless. -/
theorem dcl_union_dcl (hK : K ⊨ TE) (X Y : Set K) :
    @Work.WilC2.Dcl K (reductStruct K) (@Work.WilC2.Dcl K (reductStruct K) X ∪ Y)
      = @Work.WilC2.Dcl K (reductStruct K) (X ∪ Y) := by
  refine le_antisymm ?_ ?_
  · have h1 : @Work.WilC2.Dcl K (reductStruct K) (@Work.WilC2.Dcl K (reductStruct K) X ∪ Y)
        ⊆ @Work.WilC2.Dcl K (reductStruct K) (@Work.WilC2.Dcl K (reductStruct K) (X ∪ Y)) :=
      Work.WilC2.dcl_mono (Set.union_subset (Work.WilC2.dcl_mono Set.subset_union_left)
        (fun z hz => subset_dcl (Or.inr hz)))
    rwa [dcl_idem_reduct (K := K) hK (X ∪ Y)] at h1
  · refine Work.WilC2.dcl_mono ?_
    intro z hz
    rcases hz with hz | hz
    · exact Set.mem_union_left _ (subset_dcl hz)
    · exact Set.mem_union_right _ hz

/-! ## 2. The tower `Fₙ = Dcl (B ∪ {x₀, …, x_{n-1}})` -/

/-- `Fₙ = Dcl (B ∪ {x₀, …, x_{n-1}})`, the domain of the `n`-th stage of vdDMM Lemma 4.4. -/
def Fset (S : StepSeq B) (n : ℕ) : Set K :=
  @Work.WilC2.Dcl K (reductStruct K)
    ((B : Set K) ∪ Set.range (fun i : Fin n => S.xs (i : ℕ)))

theorem Fset_mono (S : StepSeq B) : Monotone (Fset S) := by
  intro m n hmn
  refine Work.WilC2.dcl_mono (Set.union_subset (fun x hx => Or.inl hx) ?_)
  rintro x ⟨i, rfl⟩
  exact Or.inr ⟨⟨(i : ℕ), lt_of_lt_of_le i.2 hmn⟩, rfl⟩

theorem B_subset_Fset (S : StepSeq B) (n : ℕ) : (B : Set K) ⊆ Fset S n :=
  fun x hx => subset_dcl (Or.inl hx)

theorem xs_mem_Fset (S : StepSeq B) {i n : ℕ} (h : i < n) : S.xs i ∈ Fset S n :=
  subset_dcl (Or.inr ⟨⟨i, h⟩, rfl⟩)

/-- Each `Fₙ` is closed under the definable closure. -/
theorem Fset_dcl (hK : K ⊨ TE) (S : StepSeq B) (n : ℕ) :
    @Work.WilC2.Dcl K (reductStruct K) (Fset S n) ⊆ Fset S n := by
  dsimp only [Fset]
  rw [dcl_idem_reduct (K := K) hK]

/-- The zeroth stage is `B` itself. -/
theorem Fset_zero (S : StepSeq B)
    (hBdcl : @Work.WilC2.Dcl K (reductStruct K) (B : Set K) ⊆ (B : Set K)) :
    Fset S 0 = (B : Set K) := by
  have hempty : Set.range (fun i : Fin 0 => S.xs (i : ℕ)) = (∅ : Set K) := by
    ext x; simp
  dsimp only [Fset]
  rw [hempty, Set.union_empty]
  exact le_antisymm hBdcl subset_dcl

/-- The successor stage in the form used by the iteration: `F_{n+1} = Dcl (Fₙ ∪ {xₙ})`. -/
theorem Fset_succ_shift (hK : K ⊨ TE) (S : StepSeq B) (n : ℕ) :
    Fset S (n + 1) = @Work.WilC2.Dcl K (reductStruct K) (Fset S n ∪ {S.xs n}) := by
  have hrange : Set.range (fun i : Fin (n + 1) => S.xs (i : ℕ))
      = Set.range (fun i : Fin n => S.xs (i : ℕ)) ∪ {S.xs n} := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      rcases Nat.lt_or_ge (i : ℕ) n with h | h
      · exact Or.inl ⟨⟨(i : ℕ), h⟩, rfl⟩
      · refine Or.inr ?_
        have hi : ((i : Fin (n + 1)) : ℕ) = n := le_antisymm (Nat.lt_succ_iff.mp i.2) h
        simp only [Set.mem_singleton_iff]
        exact congrArg S.xs hi
    · rintro (⟨i, rfl⟩ | hx)
      · exact ⟨⟨(i : ℕ), Nat.lt_succ_of_lt i.2⟩, rfl⟩
      · rw [Set.mem_singleton_iff] at hx
        exact ⟨⟨n, Nat.lt_succ_self n⟩, hx.symm⟩
  dsimp only [Fset]
  rw [hrange, dcl_union_dcl (K := K) hK ((B : Set K) ∪ Set.range (fun i : Fin n => S.xs (i : ℕ)))
    {S.xs n}, Set.union_assoc]

/-- The tower as an `LRc`-substructure of `K`, with carrier *definitionally* `Fset S n`. -/
noncomputable def Fsub (hK : K ⊨ TE) (S : StepSeq B) (n : ℕ) :
    LRc.Substructure K where
  carrier := Fset S n
  fun_mem := fun {m} f x hx => Fset_dcl hK S n (term_realize_mem_dcl (Functions.term f) x hx)

@[simp] theorem Fsub_coe (hK : K ⊨ TE) (S : StepSeq B) (n : ℕ) :
    (Fsub hK S n : Set K) = Fset S n := rfl

theorem Fset_mem_Fsub (hK : K ⊨ TE) (S : StepSeq B) (n : ℕ) {w : K} :
    w ∈ Fset S n ↔ w ∈ (Fsub hK S n : Set K) := by
  rw [Fsub_coe hK S n]

theorem B_mem_Fsub (hK : K ⊨ TE) (S : StepSeq B) (n : ℕ) {b : K} (hb : b ∈ (B : Set K)) :
    b ∈ (Fsub hK S n : Set K) := by
  rw [Fsub_coe hK S n]
  exact B_subset_Fset S n hb

theorem xs_mem_Fsub (hK : K ⊨ TE) (S : StepSeq B) {i n : ℕ} (h : i < n) :
    S.xs i ∈ (Fsub hK S n : Set K) := by
  rw [Fsub_coe hK S n]
  exact xs_mem_Fset S h

theorem Fsub_dcl (hK : K ⊨ TE) (S : StepSeq B) (n : ℕ) :
    @Work.WilC2.Dcl K (reductStruct K) (Fsub hK S n : Set K) ⊆ (Fsub hK S n : Set K) := by
  rw [Fsub_coe hK S n]
  exact Fset_dcl hK S n

end StepSeq

/-! ## 3. The `L`-side sequence `yₙ` -/

namespace StepSeq

variable {K L : Type} [LEc.Structure K] [LEc.Structure L] [Field L]
variable {B : LRc.Substructure K}

/-- **The `L`-side sequence of vdDMM Lemma 4.4.**  Given `y₀ : L` (intended to realise the image
under `τ` of the cut of `x₀` over `B`), put `y_{n+1} = εₙ (log yₙ − τ βₙ)`, so that
`log yₙ = τ βₙ + εₙ y_{n+1}` holds by construction. -/
def ys (B : LRc.Substructure K) (τ : LRc.Embedding B L) (S : StepSeq B) (y0 : L) : ℕ → L
  | 0 => y0
  | (n + 1) => if S.pos n then logFun (ys B τ S y0 n) - (τ (S.beta n) : L)
               else (τ (S.beta n) : L) - logFun (ys B τ S y0 n)

/-- The defining relation of the `L`-side sequence: `log yₙ = τ βₙ ± y_{n+1}`, with the sign `εₙ`
recorded by `S.pos n`. -/
theorem ys_rel (B : LRc.Substructure K) (τ : LRc.Embedding B L) (S : StepSeq B) (y0 : L)
    (n : ℕ) :
    logFun (ys B τ S y0 n)
      = (if S.pos n then (τ (S.beta n) : L) + ys B τ S y0 (n + 1)
         else (τ (S.beta n) : L) - ys B τ S y0 (n + 1)) := by
  cases hp : S.pos n
  · show logFun (ys B τ S y0 n) = (τ (S.beta n) : L) - ys B τ S y0 (n + 1)
    rw [ys]
    simp only [hp, Bool.false_eq_true, if_false]
    ring
  · show logFun (ys B τ S y0 n) = (τ (S.beta n) : L) + ys B τ S y0 (n + 1)
    rw [ys]
    simp only [hp, if_true]
    ring

end StepSeq

end Work.WilC5
