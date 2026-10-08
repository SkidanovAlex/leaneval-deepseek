import Submission.Work.Models.Port.Sz.TwoGroup
import Submission.Work.Models.Port.Sz.TwoTransitive
import Submission.Work.Models.Port.Sz.SuzukiCondition
import Submission.Work.Models.Port.Sz.StronglyEmbedded
import Submission.Work.Models.Port.Sz.Simple
import Submission.Work.Models.Port.Sz.Weyl
import Submission.Work.ZassenhausSuzuki.Defs
import Submission.Work.ZassenhausSuzuki.ModelDatum

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The model `Sz(2^(2n+1))` in the coordinates `A(GF(2^(2n+1)), θ)`

D2 of the lead's design note (`NOTES_LEAD_probe1945.md`), reduced to its two computational
parts.  Writing `K = GF(2^(2n+1))` and `θ = titsTheta n` (`x ↦ x ^ 2^(n+1)`):

* `szAEquivSzTwoGroupS` — the **coordination** of the root group: the multiplication law
  `szUg_mul` of the Suzuki root elements (`u(a,b) u(c,d) = u(a+c, b+d+a·c^(2^(n+1)))`) is
  *literally* the law of `SzA K θ`, so `A(K,θ) ≃* ↥(szTwoGroupS n)`; the `c` field of the model
  datum is this isomorphism.
* `szSplitRankOne` — the literal model `Sz(2^(2n+1))` is a split rank-one group with
  `H = szBorelS n`, `Q = szTwoGroupS n`, `t = szWgM n`: the Borel is strongly embedded and
  2-transitive (`szBorel_stronglyEmbedded`, `szModel_isMultiplyPretransitive_two`), `w` is an
  involution outside `B` (`szWgM_mul_self`, `szWgM_notMem_szBorelS`), and
  `B ⊓ B^w = T` (`szBorelS_inf_map_conj_eq`) with `B = Q ⋊ T`
  (`szBorelS_eq_sup`, `szTS_inf_szTwoGroupS`).
* `SzFrelProp` — the remaining **matrix computation** (`f = τ`), i.e. BG 5.16–5.21 in the
  matrix model: `w u(a,b) w ∈ B w u(τ(a,b))` for every `u(a,b) ≠ 1`.  This is the `frel` field
  of the model datum; `szModelDatumTitsProp_of` turns it into `SzModelDatumTitsProp`, so D2
  holds as soon as the single identity `SzFrelProp` is proved.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.ZassenhausSuzuki

/-- The Suzuki root elements with the coordinates of `SzA (GF(2^(2n+1))) (titsTheta n)`: the
multiplication law `szUg_mul` is the law of Higman's group, since `titsTheta n c = c ^ 2^(n+1)`. -/
noncomputable def szAMonoidHom (n : ℕ) :
    SzA (GaloisField 2 (2 * n + 1)) (titsTheta n) →* Submission.Sz.szTwoGroup n where
  toFun x := ⟨Submission.Sz.szUg n x.a x.b, x.a, x.b, rfl⟩
  map_one' := by
    apply Subtype.ext
    simp only [SzA.one_a, SzA.one_b]
    exact Submission.Sz.szUg_zero n
  map_mul' x y := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, SzA.mul_a, SzA.mul_b]
    rw [Submission.Sz.szUg_mul, titsTheta_apply]

/-- **Coordination of the Suzuki root group** (BG Example 5.2 / Lemma 5.1): the root group of
the Borel of `Sz(2^(2n+1))` is Higman's `A(GF(2^(2n+1)), θ)`. -/
noncomputable def szAEquivSzTwoGroup (n : ℕ) :
    SzA (GaloisField 2 (2 * n + 1)) (titsTheta n) ≃* Submission.Sz.szTwoGroup n :=
  MulEquiv.ofBijective (szAMonoidHom n) ⟨fun x y h => by
      have hp : (x.a, x.b) = (y.a, y.b) :=
        @Submission.Sz.szUg_injective n (x.a, x.b) (y.a, y.b)
          (show Submission.Sz.szUg n (x.a, x.b).1 (x.a, x.b).2 =
              Submission.Sz.szUg n (y.a, y.b).1 (y.a, y.b).2 from Subtype.ext_iff.mp h)
      exact SzA.ext (congrArg Prod.fst hp) (congrArg Prod.snd hp),
    fun y => by
      obtain ⟨a, b, hab⟩ := y.2
      exact ⟨⟨a, b⟩, Subtype.ext hab.symm⟩⟩

/-- The same coordination, with the root group viewed inside `SzModel n`. -/
noncomputable def szAEquivSzTwoGroupS (n : ℕ) :
    SzA (GaloisField 2 (2 * n + 1)) (titsTheta n) ≃* ↥(Submission.Sz.szTwoGroupS n) :=
  (szAEquivSzTwoGroup n).trans
    (Subgroup.subgroupOfEquivOfLe (Submission.Sz.szTwoGroup_le_szModel n)).symm

/-- The Weyl element is an involution. -/
theorem szWgM_mul_self (n : ℕ) : Submission.Sz.szWgM n * Submission.Sz.szWgM n = 1 := by
  apply Subtype.ext
  show (Submission.Sz.szWg n : GL (Fin 4) (Submission.Sz.SzField n)) * Submission.Sz.szWg n = 1
  exact Submission.Sz.szWg_mul_self n

/-- **The rank-one structure of the model `Sz(2^(2n+1))`.** -/
theorem szSplitRankOne (n : ℕ) (hn : 1 ≤ n) :
    IsSplitRankOne (Submission.Sz.szBorelS n) (Submission.Sz.szTwoGroupS n)
      (Submission.Sz.szWgM n) := by
  have htp : twoPoint (Submission.Sz.szBorelS n) (Submission.Sz.szWgM n) =
      Submission.Sz.szTS n :=
    Submission.Sz.szBorelS_inf_map_conj_eq n
  refine
    { stronglyEmbedded := Submission.Sz.szBorel_stronglyEmbedded n hn
      twoTransitive := Submission.Sz.szModel_isMultiplyPretransitive_two n
      invol := orderOf_eq_prime (by rw [pow_two]; exact szWgM_mul_self n) (by
        intro h1
        exact Submission.Sz.szWgM_notMem_szBorelS n (h1 ▸ Subgroup.one_mem _))
      not_mem := Submission.Sz.szWgM_notMem_szBorelS n
      le := Submission.Sz.szTwoGroupS_le_szBorelS n
      normal := by
        rw [Submission.Sz.normalizer_szTwoGroupS n]
      inf_eq := by rw [htp]; exact Submission.Sz.szTS_inf_szTwoGroupS n
      sup_eq := by rw [htp, ← Submission.Sz.szBorelS_eq_sup n] }

/-- **The `f`-relation of the model, in coordinates** (`f = τ`, BG 5.16–5.21 in the matrix
model): for every `u = (a,b) ≠ 1` there is `m ∈ B` with
`w · u(a,b) · w = m · w · u(τ(a,b))`.

This is the only matrix computation of D2; `szModelDatumTitsProp_of` derives the model datum
from it.  The `GF(8)` numerical check of this identity (uniqueness of the `B w y` representative
and `y = τ(a,b)`) is recorded in `README.md`. -/
def SzFrelProp : Prop :=
  ∀ (n : ℕ), 1 ≤ n →
    ∀ u : SzA (GaloisField 2 (2 * n + 1)) (titsTheta n), u ≠ 1 →
      ∃ m ∈ Submission.Sz.szBorelS n,
        Submission.Sz.szWgM n *
            ((szAEquivSzTwoGroupS n u : ↥(Submission.Sz.szTwoGroupS n)) :
              LeanEval.GroupTheory.Defs.SzModel n) *
            Submission.Sz.szWgM n
          = m * Submission.Sz.szWgM n *
              ((szAEquivSzTwoGroupS n (SzA.sigma (titsTheta n) u) :
                  ↥(Submission.Sz.szTwoGroupS n)) :
                LeanEval.GroupTheory.Defs.SzModel n)

/-- **D2.**  The model datum of `SzModel n` over `A(GF(2^(2n+1)), titsTheta n)`, from the
`f`-relation `SzFrelProp` alone. -/
theorem szModelDatumTitsProp_of (h : SzFrelProp) : SzModelDatumTitsProp := by
  intro n hn
  exact ⟨
    { H := Submission.Sz.szBorelS n
      Q := Submission.Sz.szTwoGroupS n
      t := Submission.Sz.szWgM n
      split := szSplitRankOne n hn
      simple := Submission.Sz.isSimpleGroup_SzModel n hn
      c := szAEquivSzTwoGroupS n
      frel := fun u hu => h n hn u hu }⟩

end Work.ZassenhausSuzuki
