import Mathlib
import Submission.Work.SSGRoute.lns3.TwoTwoPort
import Submission.Work.SSGRoute.FlowGroupSuccDefs
import Submission.Work.SSGRoute.two_torsion_assembly
import Submission.Work.SSGRoute.prop5.Surj
import Submission.Work.SSGRoute.GSDTransferAux
import Submission.Work.SSGRoute.prop5Data_exists
import Submission.Work.SSGRoute.PowRigidity.gradedStepPowMemImp
import Submission.Work.Shrinking.FreeOperator
import Submission.Work.CohomologicalShrinking.Functorial
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The `(3,2)` graded step at `p = 2`, in the cone avoiding `prop5.magnus_leadingTerm`

This module proves

> `Work.SSGRoute.gradedStep_three_two_reduced` — the off-diagonal graded step at `τ = (3,2)`
> (Schmidt–Wingberg, §2) for an arbitrary finite group `G` and an involution `δ ≠ 1`,

*without* importing `Submission.Work.SSGRoute.gradedStepOfDiagonalAt` (whose cone reaches
`prop5.magnus_leadingTerm`) nor anything reaching `prop5.adjacent_pSeries_inter_lcs_le`, so that it
can be used together with the `(3,3)` diagonal step (either `Work.SSGRoute.gradedStep_three_three`
or, better, its vendored copy `Submission/Work/SSGRoute/lns3zz3/ThreeThree.lean`) and the rest of
the `lns3`/`lns3zz3`-side development.

The file is a self-contained copy of the `(2,2)`-to-`(3,2)` reduction (`Submission/Work/SSGRoute/
gradedStep_of_diagonal.lean` specialised to a single diagonal instance, `gradedStepOfDiagonalAt.lean`)
placed in the namespace `Work.SSGRoute.RedDiag`:

* the transfer `transferPowGeneral` and its inputs (`Work.SSGRoute.GSDTransferAux` is in the cone);
* the `2`-power rigidity `inj_aux` and the surjectivity bookkeeping `surj_aux`;
* the assembly `main_aux_at` / `gradedStep_of_diagonal_at`, which turn the diagonal step at `(j,j)`
  into the graded step at `(i,j)` for every `i ≥ j`.

The only input of `gradedStep_of_diagonal.lean` that used to be universe-polymorphic through the
`prop5.magnus_leadingTerm` side is its `gen_aux` (generation of the graded piece `E(j+k,j)` by
`2^k`-th powers of the `j`-fold commutator words).  Here `gen_aux` is instead proved from the
universe-`0` version `Work.SSGRoute.prop5.pSeries_inter_lcs_le_commWordPow_sup` (Proposition 5 /
Lemma 4(ii) of `prop5/`, whose cone is clean): the honest universe-`0` statement
`gen_aux_honest_univ` for a free group on an arbitrary finite *type* `X` is transported along the
identification `Fin n × G ≃ Fin n × Fin (card G)` of the free bases (`gen_aux_honest`) — the
filtration terms are carried by the free group on the set `Fin n × G` alone, so cardinality is the
only relevant invariant.

The target is then `gradedStep_of_diagonal_at` at `j = 2`, fed with the diagonal step at `(2,2)`
taken from the *vendored* copy `Submission/Work/SSGRoute/lns3/TwoTwoPort.lean`
(`Work.SSGRoute.LNS3A.two_two_graded_step`) rather than from `Work.SSGRoute.gradedStep_two_two`:
the latter's cone contains `Work.SSGRoute.TwoTwoStep`, whose internal name `Work.SSGRoute.V`
collides with the `Work.SSGRoute.V` of the Magnus degree-`4` chain (`bf4_defs`), so importing it
would prevent this module from being used together with the `(4,4)` diagonal step
(`Work.SSGRoute.diagonal_four_general` or its vendored copy
`Work.SSGRoute.LNS3B.diagonal_four_general`).  With the vendored copy the cone of this module
contains neither `prop5.magnus_leadingTerm`, nor `prop5.adjacent_pSeries_inter_lcs_le`, nor
`Work.SSGRoute.TwoTwoStep`/`bf4_defs`, so it is compatible with both the `lns3`/`lns3zz3` side and
the `(4,4)`-Magnus side of the workspace.
-/

namespace Work.SSGRoute

open Work.CohomologicalShrinking

open scoped commutatorElement

namespace RedDiag

variable {P : Type*} [Group P]

/-- The free-group isomorphism induced by an equivalence of bases commutes with the `j`-fold
commutator word. -/
theorem freeGroupCongr_commWord {Y Z : Type*} (e : Y ≃ Z) (j : ℕ) (x : Fin j → FreeGroup Y) :
    FreeGroup.freeGroupCongr e (Work.SSGRoute.prop5.commWord j x) =
      Work.SSGRoute.prop5.commWord j (fun t => FreeGroup.freeGroupCongr e (x t)) := by
  match j, x with
  | 0, x => simp [Work.SSGRoute.prop5.commWord]
  | 1, x => simp [Work.SSGRoute.prop5.commWord]
  | (k + 2), x =>
      rw [Work.SSGRoute.prop5.commWord_succ_succ, Work.SSGRoute.prop5.commWord_succ_succ,
        map_commutatorElement, freeGroupCongr_commWord e (k + 1) (fun t : Fin (k + 1) => x t.succ)]

/-- An isomorphism of groups maps the refined term onto the refined term. -/
theorem map_refinedTerm_eq_of_mulEquiv {A B : Type*} [Group A] [Group B]
    (Φ : A ≃* B) (i j : ℕ) :
    (Work.CohomologicalShrinking.refinedTerm 2 A i j).map Φ.toMonoidHom
      = Work.CohomologicalShrinking.refinedTerm 2 B i j := by
  refine le_antisymm
    (Work.CohomologicalShrinking.map_refinedTerm_le_of_surjective 2 Φ.toMonoidHom
      Φ.surjective i j) ?_
  have h2 : (Work.CohomologicalShrinking.refinedTerm 2 B i j).map Φ.symm.toMonoidHom
      ≤ Work.CohomologicalShrinking.refinedTerm 2 A i j :=
    Work.CohomologicalShrinking.map_refinedTerm_le_of_surjective 2 Φ.symm.toMonoidHom
      Φ.symm.surjective i j
  have h3 := Subgroup.map_mono (f := Φ.toMonoidHom) h2
  rw [Subgroup.map_map] at h3
  have hcomp : Φ.toMonoidHom.comp Φ.symm.toMonoidHom = MonoidHom.id B := by
    ext z; simp
  rw [hcomp, Subgroup.map_id] at h3
  exact h3

/-- **Proposition 5 (surjectivity), honest form, universe `0`.**  The refined term `F^{(j+k,j)}`
of a free group `F` on a finite type `X` is generated, modulo `F^{(j+k,j+1)}`, by the `2^k`-th
powers of the `j`-fold commutator words. -/
theorem gen_aux_honest_univ (X : Type) [Fintype X] (j k : ℕ) (hj : 1 ≤ j) (hk : 1 ≤ k) :
    Work.CohomologicalShrinking.refinedTerm 2 (FreeGroup X) (j + k) j ≤
      Subgroup.closure {y : FreeGroup X |
        ∃ x : Fin j → FreeGroup X,
          y = (Work.SSGRoute.prop5.commWord j x) ^ (2 ^ k)} ⊔
      Work.CohomologicalShrinking.refinedTerm 2 (FreeGroup X) (j + k) (j + 1) := by
  have h := Work.SSGRoute.prop5.pSeries_inter_lcs_le_commWordPow_sup 2 X (j + k) j
    (by omega) (by omega)
  rw [show j + k - j = k from by omega] at h
  rw [Work.CohomologicalShrinking.tauSucc_of_lt (by omega : j < j + k)] at h
  show Work.CohomologicalShrinking.refinedTerm 2 (FreeGroup X) (j + k) j ≤ _
  rw [show Work.CohomologicalShrinking.refinedTerm 2 (FreeGroup X) (j + k) j
      = (Work.CohomologicalShrinking.pSeries 2 (FreeGroup X) (j + k) ⊓
          Work.CohomologicalShrinking.centralSeries (FreeGroup X) j) ⊔
        Work.CohomologicalShrinking.pSeries 2 (FreeGroup X) (j + k + 1)
      from rfl]
  refine sup_le h ?_
  exact le_trans le_sup_right le_sup_right

theorem transfer_step_identity (A U V : P) :
    (U * U)⁻¹ * (A * A) * (V * V)⁻¹
      = U⁻¹ * (U⁻¹ * A * V⁻¹) * V * U * (U⁻¹ * A * V⁻¹) * V⁻¹ := by
  group

/-- If `z` commutes with `a` and `b` and `z * z = 1`, then `a⁻¹ z b a z b⁻¹ = a⁻¹ b a b⁻¹`. -/
theorem central_sq_one_conj {Q : Type*} [Group Q] {z a b : Q}
    (hb : z * b = b * z) (ha : a * z = z * a) (hz2 : z * z = 1) :
    a⁻¹ * z * b * a * z * b⁻¹ = a⁻¹ * b * a * b⁻¹ := by
  have hza : z * b * a * z = z * z * (b * a) := by
    calc z * b * a * z = (z * b) * (a * z) := by group
      _ = (b * z) * (z * a) := by rw [hb, ha]
      _ = b * (z * z) * a := by group
      _ = b * 1 * a := by rw [hz2]
      _ = b * a := by group
      _ = z * z * (b * a) := by rw [hz2]; group
  calc a⁻¹ * z * b * a * z * b⁻¹
      = a⁻¹ * (z * b * a * z) * b⁻¹ := by group
    _ = a⁻¹ * (z * z * (b * a)) * b⁻¹ := by rw [hza]
    _ = a⁻¹ * b * a * b⁻¹ := by rw [hz2]; group

/-- **One step of the `P`-part of the transfer**: if `W ∈ P_{a+c+j}`, `U ∈ P_{a+j+1}` and
`V ∈ P_{c+j+1}`, then `U⁻¹·W·V·U·W·V⁻¹ ∈ P_{a+c+j+1}`. -/
theorem transfer_step_pSeries (a c j : ℕ) (hacj : 1 ≤ a + c + j) {U V W : P}
    (hW : W ∈ Work.CohomologicalShrinking.pSeries 2 P (a + c + j))
    (hU : U ∈ Work.CohomologicalShrinking.pSeries 2 P (a + j + 1))
    (hV : V ∈ Work.CohomologicalShrinking.pSeries 2 P (c + j + 1)) :
    U⁻¹ * W * V * U * W * V⁻¹ ∈ Work.CohomologicalShrinking.pSeries 2 P (a + c + j + 1) := by
  haveI hN : (Work.CohomologicalShrinking.pSeries 2 P (a + c + j + 1)).Normal := by
    rw [show Work.CohomologicalShrinking.pSeries 2 P (a + c + j + 1) =
      Work.Shrinking.pCentralSeries 2 P (a + c + j) from rfl]
    infer_instance
  let φ : P →* P ⧸ Work.CohomologicalShrinking.pSeries 2 P (a + c + j + 1) :=
    QuotientGroup.mk' _
  have hφ0 : ∀ z : P, z ∈ Work.CohomologicalShrinking.pSeries 2 P (a + c + j + 1) → φ z = 1 := by
    intro z hz
    rw [show φ z = QuotientGroup.mk z from rfl, QuotientGroup.eq_one_iff]
    exact hz
  have hφ1 : ∀ z : P, φ z = 1 → z ∈ Work.CohomologicalShrinking.pSeries 2 P (a + c + j + 1) := by
    intro z hz
    rw [show φ z = QuotientGroup.mk z from rfl, QuotientGroup.eq_one_iff] at hz
    exact hz
  apply hφ1
  have hW2 : W * W ∈ Work.CohomologicalShrinking.pSeries 2 P (a + c + j + 1) := by
    have h := Work.SSGRoute.GSDTransferAux.pow2_mem_pSeries P (a + c + j) hacj hW
    rwa [pow_two] at h
  have hWcomm : ∀ w : P, ⁅W, w⁆ ∈ Work.CohomologicalShrinking.pSeries 2 P (a + c + j + 1) := by
    intro w
    have h := (Work.Shrinking.commutator_le_pCentralSeries_succ 2 P (a + c + j - 1)).1
      (Subgroup.commutator_mem_commutator hW (Subgroup.mem_top w))
    rwa [show a + c + j - 1 + 1 = a + c + j from by omega] at h
  have hWc : ∀ w : P, Commute (φ W) (φ w) := by
    intro w
    rw [← commutatorElement_eq_one_iff_commute, ← map_commutatorElement]
    exact hφ0 _ (hWcomm w)
  have hz2 : φ W * φ W = 1 := by
    have h : φ (W * W) = 1 := hφ0 _ hW2
    rwa [map_mul] at h
  have hUV : ⁅U⁻¹, V⁆ ∈ Work.CohomologicalShrinking.pSeries 2 P (a + c + j + 1) := by
    have h := Work.SSGRoute.GSDTransferAux.commutator_pSeries_le P (a + j + 1) (c + j + 1)
      (by omega) (by omega)
      (Subgroup.commutator_mem_commutator (Subgroup.inv_mem _ hU) hV)
    rw [show a + j + 1 + (c + j + 1) = a + c + 2 * j + 2 from by omega] at h
    exact Work.CohomologicalShrinking.pSeries_antitone 2 P (by omega) h
  simp only [map_mul, map_inv]
  rw [central_sq_one_conj (z := φ W) (a := φ U) (b := φ V) (hWc V).eq ((hWc U).eq).symm hz2]
  have hthis : (φ U)⁻¹ * φ V * φ U * (φ V)⁻¹ = φ (⁅U⁻¹, V⁆) := by
    rw [map_commutatorElement]
    simp only [map_inv, commutatorElement_def, inv_inv]
  rw [hthis, hφ0 _ hUV]

/-- **`P`-part of the transfer.** For `x ∈ P_a`, `y ∈ P_c` and `k ≥ 1`,
`(x^(2^k))⁻¹·(x·y)^(2^k)·(y^(2^k))⁻¹ ∈ P_{a+c+k-1}`. -/
theorem powMk_mul_inv_pSeries (a c : ℕ) (ha : 1 ≤ a) (hc : 1 ≤ c) (k : ℕ) (hk : 1 ≤ k)
    {x y : P} (hx : x ∈ Work.CohomologicalShrinking.pSeries 2 P a)
    (hy : y ∈ Work.CohomologicalShrinking.pSeries 2 P c) :
    (x ^ (2 ^ k))⁻¹ * (x * y) ^ (2 ^ k) * (y ^ (2 ^ k))⁻¹ ∈
      Work.CohomologicalShrinking.pSeries 2 P (a + c + k - 1) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have key : ∀ j : ℕ,
      (x ^ (2 ^ (j + 1)))⁻¹ * (x * y) ^ (2 ^ (j + 1)) * (y ^ (2 ^ (j + 1)))⁻¹ ∈
        Work.CohomologicalShrinking.pSeries 2 P (a + c + (j + 1) - 1) := by
    intro j
    induction j with
    | zero =>
        rw [show (2 : ℕ) ^ (0 + 1) = 2 from by norm_num,
          show a + c + (0 + 1) - 1 = a + c from by omega]
        have h1 : (x ^ 2)⁻¹ * (x * y) ^ 2 * (y ^ 2)⁻¹ = x⁻¹ * ⁅y, x⁆ * x := by
          simp only [commutatorElement_def, pow_two]; group
        rw [h1]
        haveI hN : (Work.CohomologicalShrinking.pSeries 2 P (a + c)).Normal := by
          rw [show Work.CohomologicalShrinking.pSeries 2 P (a + c) =
            Work.Shrinking.pCentralSeries 2 P (a + c - 1) from rfl]
          infer_instance
        have hc0 : ⁅y, x⁆ ∈ Work.CohomologicalShrinking.pSeries 2 P (a + c) := by
          have h := Work.SSGRoute.GSDTransferAux.commutator_pSeries_le P c a hc ha
            (Subgroup.commutator_mem_commutator hy hx)
          rwa [show c + a = a + c from by omega] at h
        simpa using
          (inferInstance : (Work.CohomologicalShrinking.pSeries 2 P (a + c)).Normal).conj_mem
            ⁅y, x⁆ hc0 x⁻¹
    | succ j ih =>
        rw [show a + c + (j + 1 + 1) - 1 = a + c + j + 1 from by omega]
        have hWmem : (x ^ (2 ^ (j + 1)))⁻¹ * (x * y) ^ (2 ^ (j + 1)) *
            (y ^ (2 ^ (j + 1)))⁻¹ ∈ Work.CohomologicalShrinking.pSeries 2 P (a + c + j) := by
          have h := ih
          rw [show a + c + (j + 1) - 1 = a + c + j from by omega] at h
          exact h
        have hUm : x ^ (2 ^ (j + 1)) ∈
            Work.CohomologicalShrinking.pSeries 2 P (a + j + 1) := by
          have h := Work.SSGRoute.GSDTransferAux.pow_mem_pSeries P a (j + 1) ha hx
          rwa [show a + (j + 1) = a + j + 1 from by omega] at h
        have hVm : y ^ (2 ^ (j + 1)) ∈
            Work.CohomologicalShrinking.pSeries 2 P (c + j + 1) := by
          have h := Work.SSGRoute.GSDTransferAux.pow_mem_pSeries P c (j + 1) hc hy
          rwa [show c + (j + 1) = c + j + 1 from by omega] at h
        rw [show x ^ (2 ^ (j + 2)) = (x ^ (2 ^ (j + 1))) * (x ^ (2 ^ (j + 1))) from by
              rw [show j + 2 = (j + 1) + 1 from by omega, pow_succ, pow_mul, pow_two],
            show (x * y) ^ (2 ^ (j + 2)) =
                ((x * y) ^ (2 ^ (j + 1))) * ((x * y) ^ (2 ^ (j + 1))) from by
              rw [show j + 2 = (j + 1) + 1 from by omega, pow_succ, pow_mul, pow_two],
            show y ^ (2 ^ (j + 2)) = (y ^ (2 ^ (j + 1))) * (y ^ (2 ^ (j + 1))) from by
              rw [show j + 2 = (j + 1) + 1 from by omega, pow_succ, pow_mul, pow_two]]
        rw [transfer_step_identity ((x * y) ^ (2 ^ (j + 1))) (x ^ (2 ^ (j + 1)))
          (y ^ (2 ^ (j + 1)))]
        exact transfer_step_pSeries a c j (by omega) hWmem hUm hVm
  exact key j

/-- **The graded-step transfer.** For `x ∈ F^{(a,b)}`, `y ∈ F^{(c,d)}` and `k ≥ 1`,
`(x^(2^k))⁻¹·(x·y)^(2^k)·(y^(2^k))⁻¹ ∈ F^{(a+c+k-1, b+d)}`. -/
theorem transferPowGeneral (P : Type*) [Group P]
    (a b c d k : ℕ) (ha : 1 ≤ a) (hc : 1 ≤ c) (hk : 1 ≤ k)
    {x y : P} (hx : x ∈ Work.CohomologicalShrinking.refinedTerm 2 P a b)
    (hy : y ∈ Work.CohomologicalShrinking.refinedTerm 2 P c d) :
    (x ^ (2 ^ k))⁻¹ * (x * y) ^ (2 ^ k) * (y ^ (2 ^ k))⁻¹ ∈
      Work.CohomologicalShrinking.refinedTerm 2 P (a + c + k - 1) (b + d) := by
  have hxP : x ∈ Work.CohomologicalShrinking.pSeries 2 P a :=
    Work.CohomologicalShrinking.refinedTerm_le_pSeries 2 P a b hx
  have hyP : y ∈ Work.CohomologicalShrinking.pSeries 2 P c :=
    Work.CohomologicalShrinking.refinedTerm_le_pSeries 2 P c d hy
  have hcomm : ⁅y, x⁆ ∈ Work.CohomologicalShrinking.centralSeries P (b + d) ⊔
      Work.CohomologicalShrinking.pSeries 2 P (a + c + 1) :=
    Work.SSGRoute.GSDTransferAux.commutator_refinedTerm_mem P a b c d ha hc hx hy
  have hc0P : ⁅y, x⁆ ∈ Work.CohomologicalShrinking.pSeries 2 P (a + c) := by
    have h := Work.SSGRoute.GSDTransferAux.commutator_pSeries_le P c a hc ha
      (Subgroup.commutator_mem_commutator hyP hxP)
    rwa [show c + a = a + c from by omega] at h
  have hc0k : ⁅y, x⁆ ^ (2 ^ (k - 1)) ∈
      Work.CohomologicalShrinking.pSeries 2 P (a + c + k - 1) := by
    have h := Work.SSGRoute.GSDTransferAux.pow_mem_pSeries P (a + c) (k - 1) (by omega) hc0P
    rwa [show a + c + (k - 1) = a + c + k - 1 from by omega] at h
  -- the `P`-part: `(x^(2^k))⁻¹·(x·y)^(2^k)·(y^(2^k))⁻¹`
  have hE := powMk_mul_inv_pSeries a c ha hc k hk hxP hyP
  -- the auxiliary element `m = (x·y)^(2^k)·([y,x]^(2^(k-1)))⁻¹·(x^(2^k)·y^(2^k))⁻¹`
  set m : P := (x * y) ^ (2 ^ k) * (⁅y, x⁆ ^ (2 ^ (k - 1)))⁻¹ *
      ((x ^ (2 ^ k)) * (y ^ (2 ^ k)))⁻¹ with hmdef
  -- `m` lies in the `γ`-part (this is the colleague's `engine`)
  have hmγ : m ∈ Work.CohomologicalShrinking.centralSeries P (b + d) ⊔
      Work.CohomologicalShrinking.pSeries 2 P (a + c + k) := by
    have h := Work.SSGRoute.GSDTransferAux.engine P (a - 1) (c - 1) b d k hk
      (by rw [show a - 1 + 1 = a from by omega]; exact hxP)
      (by rw [show c - 1 + 1 = c from by omega]; exact hyP)
      (by rw [show a - 1 + (c - 1) + 3 = a + c + 1 from by omega]; exact hcomm)
    rwa [show a - 1 + (c - 1) + k + 2 = a + c + k from by omega] at h
  -- `m` lies in the `P`-part
  haveI hPn : (Work.CohomologicalShrinking.pSeries 2 P (a + c + k - 1)).Normal := by
    rw [show Work.CohomologicalShrinking.pSeries 2 P (a + c + k - 1) =
      Work.Shrinking.pCentralSeries 2 P (a + c + k - 1 - 1) from rfl]
    infer_instance
  have hmP : m ∈ Work.CohomologicalShrinking.pSeries 2 P (a + c + k - 1) := by
    rw [hmdef]
    rw [show (x * y) ^ (2 ^ k) * (⁅y, x⁆ ^ (2 ^ (k - 1)))⁻¹ *
          ((x ^ (2 ^ k)) * (y ^ (2 ^ k)))⁻¹
        = ((x ^ (2 ^ k)) * ((x ^ (2 ^ k))⁻¹ * (x * y) ^ (2 ^ k) * (y ^ (2 ^ k))⁻¹)
              * (x ^ (2 ^ k))⁻¹)
          * ((x ^ (2 ^ k)) * ((y ^ (2 ^ k)) * (⁅y, x⁆ ^ (2 ^ (k - 1)))⁻¹
              * (y ^ (2 ^ k))⁻¹) * (x ^ (2 ^ k))⁻¹) from by group]
    exact Subgroup.mul_mem _
      (hPn.conj_mem _ hE (x ^ (2 ^ k)))
      (hPn.conj_mem _ (hPn.conj_mem _ (Subgroup.inv_mem _ hc0k) (y ^ (2 ^ k)))
        (x ^ (2 ^ k)))
  -- the decomposition of the target element
  set D : P := (x ^ (2 ^ k))⁻¹ * (x * y) ^ (2 ^ k) * (y ^ (2 ^ k))⁻¹ with hDdef
  have hDm : D = (x ^ (2 ^ k))⁻¹ * m * (x ^ (2 ^ k)) * (y ^ (2 ^ k)) *
      ⁅y, x⁆ ^ (2 ^ (k - 1)) * (y ^ (2 ^ k))⁻¹ := by
    rw [hDdef, hmdef]
    group
  have hDP : D ∈ Work.CohomologicalShrinking.pSeries 2 P (a + c + k - 1) := by
    rw [hDdef]
    exact hE
  -- `D` also lies in the `γ`-part
  have hDγ : D ∈ Work.CohomologicalShrinking.centralSeries P (b + d) ⊔
      Work.CohomologicalShrinking.pSeries 2 P (a + c + k) := by
    haveI hpn' : (Work.CohomologicalShrinking.pSeries 2 P (a + c + k)).Normal := by
      rw [show Work.CohomologicalShrinking.pSeries 2 P (a + c + k) =
        Work.Shrinking.pCentralSeries 2 P (a + c + k - 1) from rfl]
      infer_instance
    haveI hgn : (Work.CohomologicalShrinking.centralSeries P (b + d)).Normal :=
      Subgroup.lowerCentralSeries_normal (⊤ : Subgroup P) (b + d - 1)
    haveI hTn : (Work.CohomologicalShrinking.centralSeries P (b + d) ⊔
        Work.CohomologicalShrinking.pSeries 2 P (a + c + k)).Normal :=
      Subgroup.sup_normal _ _
    have hc0T : ⁅y, x⁆ ^ (2 ^ (k - 1)) ∈ Work.CohomologicalShrinking.centralSeries P (b + d) ⊔
        Work.CohomologicalShrinking.pSeries 2 P (a + c + k) := by
      have h := Work.SSGRoute.GSDTransferAux.pow_two_pow_mem_pSeries_sup P
        (Work.CohomologicalShrinking.centralSeries P (b + d)) (a + c + 1) (k - 1)
        (by omega) hcomm
      rwa [show a + c + 1 + (k - 1) = a + c + k from by omega] at h
    rw [hDm]
    rw [show (x ^ (2 ^ k))⁻¹ * m * (x ^ (2 ^ k)) * (y ^ (2 ^ k)) *
          ⁅y, x⁆ ^ (2 ^ (k - 1)) * (y ^ (2 ^ k))⁻¹
        = ((x ^ (2 ^ k))⁻¹ * m * (x ^ (2 ^ k)))
          * ((y ^ (2 ^ k)) * ⁅y, x⁆ ^ (2 ^ (k - 1)) * (y ^ (2 ^ k))⁻¹) from by group]
    exact Subgroup.mul_mem _
      (hTn.conj_mem' m hmγ (x ^ (2 ^ k)))
      (hTn.conj_mem _ hc0T (y ^ (2 ^ k)))
  -- modular assembly
  haveI hpk : (Work.CohomologicalShrinking.pSeries 2 P (a + c + k)).Normal := by
    rw [show Work.CohomologicalShrinking.pSeries 2 P (a + c + k) =
      Work.Shrinking.pCentralSeries 2 P (a + c + k - 1) from rfl]
    infer_instance
  obtain ⟨g, hg, p, hp, hgp⟩ := Subgroup.mem_sup_of_normal_right.mp hDγ
  have hgP : g ∈ Work.CohomologicalShrinking.pSeries 2 P (a + c + k - 1) := by
    have h1 : g = D * p⁻¹ := by rw [← hgp]; group
    rw [h1]
    exact Subgroup.mul_mem _ hDP
      (Subgroup.inv_mem _ (Work.CohomologicalShrinking.pSeries_antitone 2 P (by omega) hp))
  rw [Work.CohomologicalShrinking.refinedTerm]
  rw [show a + c + k - 1 + 1 = a + c + k from by omega]
  rw [← hgp]
  exact Subgroup.mul_mem _
    (Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨hgP, hg⟩)) (Subgroup.mem_sup_right hp)

/-- `γ_j ⊆ P_j`. -/
theorem centralSeries_le_pSeries (j : ℕ) :
    Work.CohomologicalShrinking.centralSeries P j ≤
      Work.CohomologicalShrinking.pSeries 2 P j :=
  Work.ProP.lowerCentralSeries_le_pCentralSeries 2 P (j - 1)

/-- Powers of elements of `P_j` stay in the `p`-central series, raising the index. -/
theorem pow_two_pow_mem_pSeries (j k : ℕ) (hj : 1 ≤ j) {x : P}
    (hx : x ∈ Work.CohomologicalShrinking.pSeries 2 P j) :
    x ^ (2 ^ k) ∈ Work.CohomologicalShrinking.pSeries 2 P (j + k) := by
  have key : ∀ t : ℕ, x ^ (2 ^ t) ∈ Work.CohomologicalShrinking.pSeries 2 P (j + t) := by
    intro t
    induction t with
    | zero => simpa using hx
    | succ t ih =>
        have h1 : x ^ 2 ^ (t + 1) = (x ^ 2 ^ t) ^ 2 := by rw [pow_succ, pow_mul]
        rw [h1]
        have h2 : (x ^ 2 ^ t) ^ 2 ∈ Work.Shrinking.pCentralSeries 2 P ((j + t) - 1 + 1) :=
          Work.Shrinking.pow_mem_pCentralSeries_succ 2 P ih
        have hidx : (j + t) - 1 + 1 = j + (t + 1) - 1 := by omega
        rw [hidx] at h2
        exact h2
  simpa [Work.CohomologicalShrinking.pSeries] using key k

/-- Monotonicity of the refinement. -/
theorem refinedTerm_mono (p : ℕ) (P : Type*) [Group P] {a a' b b' : ℕ} (ha : a' ≤ a)
    (hb : b' ≤ b) : Work.CohomologicalShrinking.refinedTerm p P a b ≤
      Work.CohomologicalShrinking.refinedTerm p P a' b' := by
  rw [Work.CohomologicalShrinking.refinedTerm, Work.CohomologicalShrinking.refinedTerm]
  refine sup_le ?_ ?_
  · exact le_trans (le_inf (le_trans inf_le_left (Work.CohomologicalShrinking.pSeries_antitone p P ha))
      (le_trans inf_le_right (Work.CohomologicalShrinking.centralSeries_antitone P hb))) le_sup_left
  · exact le_trans (Work.CohomologicalShrinking.pSeries_antitone p P (Nat.succ_le_succ ha)) le_sup_right

/-- For a normal subgroup, `a * b⁻¹ ∈ H ↔ a⁻¹ * b ∈ H`. -/
theorem mul_inv_mem_iff_inv_mul_mem {P : Type*} [Group P] {H : Subgroup P} (hN : H.Normal)
    {a b : P} : a * b⁻¹ ∈ H ↔ a⁻¹ * b ∈ H := by
  constructor
  · intro h
    have h' : b * a⁻¹ ∈ H := by simpa [mul_inv_rev] using Subgroup.inv_mem H h
    rw [show a⁻¹ * b = a⁻¹ * (b * a⁻¹) * a from by group]
    exact Subgroup.Normal.conj_mem' hN (b * a⁻¹) h' a
  · intro h
    have h' : b⁻¹ * a ∈ H := by simpa [mul_inv_rev] using Subgroup.inv_mem H h
    rw [show a * b⁻¹ = a * (b⁻¹ * a) * a⁻¹ from by group]
    exact Subgroup.Normal.conj_mem hN (b⁻¹ * a) h' a


/-- Additivity of the `2^k`-th power map on `γ_j` modulo the next refined term. -/
theorem gamma_pow_mul_mem_lcs (j k : ℕ) (hj : 2 ≤ j) {x y : P}
    (hx : x ∈ Work.CohomologicalShrinking.centralSeries P j)
    (hy : y ∈ Work.CohomologicalShrinking.centralSeries P j) :
    (x * y) ^ (2 ^ k) * ((y ^ (2 ^ k)) * (x ^ (2 ^ k)))⁻¹ ∈
      (⊤ : Subgroup P).lowerCentralSeries j := by
  have hx' : x ∈ (⊤ : Subgroup P).lowerCentralSeries (j - 1) := hx
  have hy' : y ∈ (⊤ : Subgroup P).lowerCentralSeries (j - 1) := hy
  have hxy : ⁅x, y⁆ ∈ (⊤ : Subgroup P).lowerCentralSeries j := by
    rw [show j = (j - 1) + 1 from by omega, Subgroup.lowerCentralSeries_succ]
    exact Subgroup.commutator_mono le_rfl le_top
      (Subgroup.commutator_mem_commutator hx' hy')
  set N := (⊤ : Subgroup P).lowerCentralSeries j with hN
  haveI : N.Normal := Subgroup.lowerCentralSeries_normal ⊤ j
  have hcom : Commute ((QuotientGroup.mk' N) x) ((QuotientGroup.mk' N) y) := by
    rw [commutatorElement_eq_one_iff_commute.symm, ← map_commutatorElement]
    exact (QuotientGroup.eq_one_iff _).mpr hxy
  have hkey : (QuotientGroup.mk' N) ((x * y) ^ (2 ^ k) *
      ((y ^ (2 ^ k)) * (x ^ (2 ^ k)))⁻¹) = 1 := by
    simp only [map_mul, map_inv, map_pow]
    have h2 : (QuotientGroup.mk' N) x ^ (2 ^ k) * (QuotientGroup.mk' N) y ^ (2 ^ k)
        = (QuotientGroup.mk' N) y ^ (2 ^ k) * (QuotientGroup.mk' N) x ^ (2 ^ k) :=
      Commute.pow_pow hcom (2 ^ k) (2 ^ k)
    rw [Commute.mul_pow hcom (2 ^ k), h2, mul_inv_cancel]
  exact (QuotientGroup.eq_one_iff _).mp hkey

/-- Additivity of the `2^k`-th power map on `γ_j`, in the refined-term form. -/
theorem gamma_pow_mul_mem_refined (j k : ℕ) (hj : 2 ≤ j) {x y : P}
    (hx : x ∈ Work.CohomologicalShrinking.centralSeries P j)
    (hy : y ∈ Work.CohomologicalShrinking.centralSeries P j) :
    (x * y) ^ (2 ^ k) * ((y ^ (2 ^ k)) * (x ^ (2 ^ k)))⁻¹ ∈
      Work.CohomologicalShrinking.refinedTerm 2 P (j + k) (j + 1) := by
  have hlc := gamma_pow_mul_mem_lcs j k hj hx hy
  have hxg : x ∈ Work.CohomologicalShrinking.pSeries 2 P j := centralSeries_le_pSeries j hx
  have hyg : y ∈ Work.CohomologicalShrinking.pSeries 2 P j := centralSeries_le_pSeries j hy
  have hxyP : (x * y) ^ (2 ^ k) ∈ Work.CohomologicalShrinking.pSeries 2 P (j + k) :=
    pow_two_pow_mem_pSeries j k (by omega) (Subgroup.mul_mem _ hxg hyg)
  have hyxP : (y ^ (2 ^ k) * x ^ (2 ^ k))⁻¹ ∈
      Work.CohomologicalShrinking.pSeries 2 P (j + k) :=
    Subgroup.inv_mem _
      (Subgroup.mul_mem _ (pow_two_pow_mem_pSeries j k (by omega) hyg)
        (pow_two_pow_mem_pSeries j k (by omega) hxg))
  have hP := Subgroup.mul_mem _ hxyP hyxP
  rw [Work.CohomologicalShrinking.refinedTerm]
  exact Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨hP, hlc⟩)

/-- The additivity of the `2^k`-th power map on `P_{(j,j)}`, in the order used in the assembly,
obtained from the general transfer lemma by conjugation. -/
theorem addPowRefined' (j k : ℕ) (hj : 1 ≤ j) (hk : 1 ≤ k) {x y : P}
    (hx : x ∈ Work.CohomologicalShrinking.refinedTerm 2 P j j)
    (hy : y ∈ Work.CohomologicalShrinking.refinedTerm 2 P j j) :
    ((x * y) ^ (2 ^ k))⁻¹ * (x ^ (2 ^ k) * y ^ (2 ^ k)) ∈
      Work.CohomologicalShrinking.refinedTerm 2 P (j + k) (j + 1) := by
  have hZ := transferPowGeneral P j j j j k hj hj hk hx hy
  have hconj : x ^ (2 ^ k) * ((x ^ (2 ^ k))⁻¹ * (x * y) ^ (2 ^ k) * (y ^ (2 ^ k))⁻¹)
      * (x ^ (2 ^ k))⁻¹ = (x * y) ^ (2 ^ k) * (x ^ (2 ^ k) * y ^ (2 ^ k))⁻¹ := by group
  have hmem : (x * y) ^ (2 ^ k) * (x ^ (2 ^ k) * y ^ (2 ^ k))⁻¹ ∈
      Work.CohomologicalShrinking.refinedTerm 2 P (j + k) (j + 1) := by
    have h1 : x ^ (2 ^ k) * ((x ^ (2 ^ k))⁻¹ * (x * y) ^ (2 ^ k) * (y ^ (2 ^ k))⁻¹)
        * (x ^ (2 ^ k))⁻¹ ∈
        Work.CohomologicalShrinking.refinedTerm 2 P (j + j + k - 1) (j + j) :=
      (Work.CohomologicalShrinking.refinedTerm_normal 2 P (j + j + k - 1) (j + j)).conj_mem
        _ hZ (x ^ (2 ^ k))
    rw [hconj] at h1
    exact refinedTerm_mono 2 P (by omega) (by omega) h1
  have h2 : ((x * y) ^ (2 ^ k))⁻¹ * (x ^ (2 ^ k) * y ^ (2 ^ k))
      = ((x * y) ^ (2 ^ k))⁻¹
        * (((x * y) ^ (2 ^ k) * (x ^ (2 ^ k) * y ^ (2 ^ k))⁻¹)⁻¹)
        * (((x * y) ^ (2 ^ k))⁻¹)⁻¹ := by group
  rw [h2]
  exact (Work.CohomologicalShrinking.refinedTerm_normal 2 P (j + k) (j + 1)).conj_mem
    _ (Subgroup.inv_mem _ hmem) _



/-! ## The quotient `Q(a,b)` and the map `toQ` -/

section QuotAPI

variable (G : Type*) (n : ℕ) [Group G]

/-- `Work.Shrinking.freeOperatorGroup G n(n)^{(a,b)}`. -/
noncomputable abbrev Tm (a b : ℕ) : Subgroup (Work.Shrinking.freeOperatorGroup G n) :=
  Work.CohomologicalShrinking.flowTerm 2 G n a b

/-- The quotient `Work.Shrinking.freeOperatorGroup G n(n)/Work.Shrinking.freeOperatorGroup G n(n)^{(a,b)}`. -/
noncomputable abbrev Qt (a b : ℕ) : Type _ :=
  Work.CohomologicalShrinking.flowQuotient 2 G n a b

/-- The canonical projection `Work.Shrinking.freeOperatorGroup G n(n) → Q(a,b)`, as a monoid homomorphism. -/
noncomputable def toQ (a b : ℕ) :
    Work.Shrinking.freeOperatorGroup G n →* Qt G n a b :=
  (QuotientGroup.mk' ((Tm G n a b).subgroupOf ⊤)).comp
    ((Subgroup.topEquiv (G := Work.Shrinking.freeOperatorGroup G n)).symm).toMonoidHom

variable {G n}

theorem toQ_eq_iff (a b : ℕ) (x y : Work.Shrinking.freeOperatorGroup G n) :
    toQ G n a b x = toQ G n a b y ↔ x⁻¹ * y ∈ Tm G n a b := by
  rw [toQ, MonoidHom.comp_apply, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
  exact Iff.rfl

end QuotAPI


section Main
variable (G : Type*) [Group G] [Fintype G] (n : ℕ)

/-- Bridge: `Tm` at a successor index. -/
theorem Tm_tauSucc_of_lt {i j : ℕ} (h : j < i) :
    Tm G n (Work.CohomologicalShrinking.tauSucc i j).1
        (Work.CohomologicalShrinking.tauSucc i j).2 = Tm G n i (j + 1) := by
  rw [Work.CohomologicalShrinking.tauSucc_of_lt h]

theorem Tm_tauSucc_of_le {i j : ℕ} (h : i ≤ j) :
    Tm G n (Work.CohomologicalShrinking.tauSucc i j).1
        (Work.CohomologicalShrinking.tauSucc i j).2 = Tm G n (i + 1) 1 := by
  rw [Work.CohomologicalShrinking.tauSucc_of_le h]

theorem Tm_jp1_eq_pSeries (j : ℕ) :
    Tm G n (j + 1) 1 = Work.CohomologicalShrinking.pSeries 2 (Work.Shrinking.freeOperatorGroup G n) (j + 1) := by
  show Work.CohomologicalShrinking.refinedTerm 2 (Work.Shrinking.freeOperatorGroup G n) (j + 1) 1 = _
  exact Work.CohomologicalShrinking.refinedTerm_one 2 (Work.Shrinking.freeOperatorGroup G n) (j + 1)

theorem Tm_self_eq_pSeries (j : ℕ) :
    Tm G n (Work.CohomologicalShrinking.tauSucc j j).1
        (Work.CohomologicalShrinking.tauSucc j j).2 =
      Work.CohomologicalShrinking.pSeries 2 (Work.Shrinking.freeOperatorGroup G n) (j + 1) := by
  rw [show Work.CohomologicalShrinking.tauSucc j j = (j + 1, 1) from
    Work.CohomologicalShrinking.tauSucc_of_le (le_refl j)]
  exact Tm_jp1_eq_pSeries G n j

/-- The map `toQ` is equivariant. -/
theorem gs32_toQ_smul (a b : ℕ) (g : G) (w : Work.Shrinking.freeOperatorGroup G n) :
    flowAction 2 G n a b g (toQ G n a b w) = toQ G n a b (g • w) := by
  haveI : (Tm G n a b).Normal :=
    Work.CohomologicalShrinking.refinedTerm_normal 2 (Work.Shrinking.freeOperatorGroup G n) a b
  show flowAction 2 G n a b g
      ((QuotientGroup.mk' ((Tm G n a b).subgroupOf ⊤)).comp
        (Subgroup.topEquiv (G := Work.Shrinking.freeOperatorGroup G n)).symm.toMonoidHom w)
    = (QuotientGroup.mk' ((Tm G n a b).subgroupOf ⊤)).comp
        (Subgroup.topEquiv (G := Work.Shrinking.freeOperatorGroup G n)).symm.toMonoidHom (g • w)
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply]
  have hP : (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G n)).map
      (MulDistribMulAction.toMulAut G (Work.Shrinking.freeOperatorGroup G n) g).toMonoidHom = ⊤ :=
    Subgroup.map_top_of_surjective _ (MulDistribMulAction.toMulAut G _ g).surjective
  have hK : (Tm G n a b).map (MulDistribMulAction.toMulAut G (Work.Shrinking.freeOperatorGroup G n) g).toMonoidHom = Tm G n a b :=
    Work.CohomologicalShrinking.map_refinedTerm_eq 2 _ a b
  change Work.Shrinking.quotAut ⊤ (Tm G n a b) g hP hK
      (QuotientGroup.mk' ((Tm G n a b).subgroupOf ⊤)
        (Subgroup.topEquiv.symm.toMonoidHom w)) = _
  rw [Work.Shrinking.quotAut_mk]
  exact congrArg _ (Subtype.ext (Work.Shrinking.subAut_coe ⊤ g hP
    (Subgroup.topEquiv.symm.toMonoidHom w)))

/-- Computation of `flowQuotSucc` on a `toQ`-representative. -/
theorem flowQuotSucc_toQ (i j : ℕ) (w : Work.Shrinking.freeOperatorGroup G n) :
    flowQuotSucc 2 G n i j (toQ G n (Work.CohomologicalShrinking.tauSucc i j).1
        (Work.CohomologicalShrinking.tauSucc i j).2 w) = toQ G n i j w := by
  rw [toQ]
  show flowQuotSucc 2 G n i j (QuotientGroup.mk' _ (Subgroup.topEquiv.symm.toMonoidHom w))
    = toQ G n i j w
  rw [flowQuotSucc_mk, toQ, MonoidHom.comp_apply, QuotientGroup.mk'_apply]

/-- Membership in the kernel of `flowQuotSucc`, in terms of `toQ`. -/
theorem flowQuotSucc_toQ_eq_one (i j : ℕ) (w : Work.Shrinking.freeOperatorGroup G n) :
    flowQuotSucc 2 G n i j (toQ G n (Work.CohomologicalShrinking.tauSucc i j).1
        (Work.CohomologicalShrinking.tauSucc i j).2 w) = 1 ↔ w ∈ Tm G n i j := by
  rw [flowQuotSucc_toQ, toQ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  exact Iff.rfl

/-- `T(j,j) = γ_j · P_{j+1}`. -/
theorem Tm_jj_eq (j : ℕ) :
    Tm G n j j = Work.CohomologicalShrinking.centralSeries
        (Work.Shrinking.freeOperatorGroup G n) j ⊔
      Work.CohomologicalShrinking.pSeries 2 (Work.Shrinking.freeOperatorGroup G n) (j + 1) := by
  show Work.CohomologicalShrinking.refinedTerm 2 (Work.Shrinking.freeOperatorGroup G n) j j = _
  rw [Work.CohomologicalShrinking.refinedTerm,
    inf_eq_right.mpr (centralSeries_le_pSeries (P := Work.Shrinking.freeOperatorGroup G n) j)]


/-- **The generation statement of Proposition 5 for an arbitrary `G`**: the refined term
`F^{(j+k,j)}` is generated, modulo `F^{(j+k,j+1)}`, by the `2^k`-th powers of the `j`-fold
commutator words.  Proved by transporting the universe-`0` statement `gen_aux_honest_univ` along
the identification `Fin n × G ≃ Fin n × Fin (card G)` of the free bases: the filtration terms are
carried by the free group on the set `Fin n × G` alone, so cardinality is the only relevant
invariant. -/
theorem gen_aux_honest (G : Type*) [Group G] [Fintype G] (n : ℕ) (j k : ℕ) (hj : 1 ≤ j)
    (hk : 1 ≤ k) :
    Work.CohomologicalShrinking.refinedTerm 2 (Work.Shrinking.freeOperatorGroup G n) (j + k) j ≤
      Subgroup.closure {y : Work.Shrinking.freeOperatorGroup G n |
        ∃ x : Fin j → Work.Shrinking.freeOperatorGroup G n,
          y = (Work.SSGRoute.prop5.commWord j x) ^ (2 ^ k)} ⊔
      Work.CohomologicalShrinking.refinedTerm 2 (Work.Shrinking.freeOperatorGroup G n)
        (j + k) (j + 1) := by
  classical
  let e : Fin n × G ≃ Fin n × Fin (Fintype.card G) :=
    Equiv.prodCongr (Equiv.refl (Fin n)) (Fintype.equivFin G)
  let Φ : FreeGroup (Fin n × Fin (Fintype.card G)) ≃* FreeGroup (Fin n × G) :=
    FreeGroup.freeGroupCongr e.symm
  have h0 := gen_aux_honest_univ (Fin n × Fin (Fintype.card G)) j k hj hk
  have hW : Subgroup.map Φ.toMonoidHom
      (Subgroup.closure {y : FreeGroup (Fin n × Fin (Fintype.card G)) |
        ∃ x : Fin j → FreeGroup (Fin n × Fin (Fintype.card G)),
          y = (Work.SSGRoute.prop5.commWord j x) ^ (2 ^ k)})
      ≤ Subgroup.closure {y : Work.Shrinking.freeOperatorGroup G n |
        ∃ x : Fin j → Work.Shrinking.freeOperatorGroup G n,
          y = (Work.SSGRoute.prop5.commWord j x) ^ (2 ^ k)} := by
    rw [Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
    intro y hy
    change Φ y ∈ Subgroup.closure {y : Work.Shrinking.freeOperatorGroup G n |
      ∃ x : Fin j → Work.Shrinking.freeOperatorGroup G n,
        y = (Work.SSGRoute.prop5.commWord j x) ^ (2 ^ k)}
    obtain ⟨x, rfl⟩ := hy
    refine Subgroup.subset_closure ⟨fun t => Φ (x t), ?_⟩
    rw [map_pow, freeGroupCongr_commWord e.symm j x]
  rw [← map_refinedTerm_eq_of_mulEquiv Φ (j + k) j]
  refine le_trans (Subgroup.map_mono (f := Φ.toMonoidHom) h0) ?_
  rw [Subgroup.map_sup]
  exact sup_le (le_trans hW le_sup_left)
    (le_trans (le_of_eq (map_refinedTerm_eq_of_mulEquiv Φ (j + k) (j + 1))) le_sup_right)

/-- **Generation of the graded piece** by `2^k`-th powers of `j`-fold commutator words
(Schmidt–Wingberg, Proposition 5, surjectivity). -/
theorem gen_aux (j k : ℕ) (hj : 1 ≤ j) (hk : 1 ≤ k) :
    Tm G n (j + k) j ≤
      Subgroup.closure {y : Work.Shrinking.freeOperatorGroup G n |
        ∃ x : Fin j → Work.Shrinking.freeOperatorGroup G n,
          y = (Work.SSGRoute.prop5.commWord j x) ^ (2 ^ k)} ⊔ Tm G n (j + k) (j + 1) :=
  gen_aux_honest G n j k hj hk

/-- **Injectivity** of the `2^k`-th power map on `T(j,j)` modulo the next refined term
(the "2-power rigidity" of Schmidt–Wingberg). -/
theorem inj_aux (j k : ℕ) (hj : 2 ≤ j) (hk : 1 ≤ k)
    {z₁ z₂ : Work.Shrinking.freeOperatorGroup G n}
    (h₁ : z₁ ∈ Tm G n j j) (h₂ : z₂ ∈ Tm G n j j)
    (heq : (z₁ ^ (2 ^ k))⁻¹ * (z₂ ^ (2 ^ k)) ∈ Tm G n (j + k) (j + 1)) :
    z₁⁻¹ * z₂ ∈ Tm G n (Work.CohomologicalShrinking.tauSucc j j).1
      (Work.CohomologicalShrinking.tauSucc j j).2 := by
  haveI hnorm : (Work.CohomologicalShrinking.pSeries 2
      (Work.Shrinking.freeOperatorGroup G n) (j + 1)).Normal :=
    Work.Shrinking.pCentralSeries_normal 2 (Work.Shrinking.freeOperatorGroup G n) j
  have hTm : Tm G n j j = Work.CohomologicalShrinking.centralSeries
        (Work.Shrinking.freeOperatorGroup G n) j ⊔
      Work.CohomologicalShrinking.pSeries 2 (Work.Shrinking.freeOperatorGroup G n) (j + 1) := by
    show Work.CohomologicalShrinking.refinedTerm 2
      (Work.Shrinking.freeOperatorGroup G n) j j = _
    rw [Work.CohomologicalShrinking.refinedTerm,
      inf_eq_right.mpr (centralSeries_le_pSeries (P := Work.Shrinking.freeOperatorGroup G n) j)]
  obtain ⟨u₁, hu₁, p₁, hp₁, hu₁p₁⟩ := (Subgroup.mem_sup_of_normal_right
    (s := Work.CohomologicalShrinking.centralSeries (Work.Shrinking.freeOperatorGroup G n) j)
    (t := Work.CohomologicalShrinking.pSeries 2 (Work.Shrinking.freeOperatorGroup G n) (j + 1))).mp
    (hTm ▸ h₁)
  obtain ⟨u₂, hu₂, p₂, hp₂, hu₂p₂⟩ := (Subgroup.mem_sup_of_normal_right
    (s := Work.CohomologicalShrinking.centralSeries (Work.Shrinking.freeOperatorGroup G n) j)
    (t := Work.CohomologicalShrinking.pSeries 2 (Work.Shrinking.freeOperatorGroup G n) (j + 1))).mp
    (hTm ▸ h₂)
  have hTm1 : u₁ ∈ Tm G n j j := hTm ▸ Subgroup.mem_sup_left hu₁
  have hTm2 : u₂ ∈ Tm G n j j := hTm ▸ Subgroup.mem_sup_left hu₂
  have hTp1 : p₁ ∈ Tm G n j j := hTm ▸ Subgroup.mem_sup_right hp₁
  have hTp2 : p₂ ∈ Tm G n j j := hTm ▸ Subgroup.mem_sup_right hp₂
  -- `p_i^(2^k)` lies in the next refined term
  have hpN : ∀ q : Work.Shrinking.freeOperatorGroup G n,
      q ∈ Work.CohomologicalShrinking.pSeries 2 (Work.Shrinking.freeOperatorGroup G n) (j + 1) →
      q ^ (2 ^ k) ∈ Tm G n (j + k) (j + 1) := by
    intro q hq
    rw [show Tm G n (j + k) (j + 1) = Work.CohomologicalShrinking.refinedTerm 2
      (Work.Shrinking.freeOperatorGroup G n) (j + k) (j + 1) from rfl,
      Work.CohomologicalShrinking.refinedTerm]
    refine Subgroup.mem_sup_right ?_
    exact Work.CohomologicalShrinking.pSeries_antitone 2
      (Work.Shrinking.freeOperatorGroup G n) (by omega)
      (pow_two_pow_mem_pSeries (j + 1) k (by omega) hq)
  -- `z_i^(2^k) ≡ u_i^(2^k)` modulo the next refined term
  have hstep : ∀ (u p z : Work.Shrinking.freeOperatorGroup G n),
      u ∈ Tm G n j j → p ∈ Tm G n j j →
      p ∈ Work.CohomologicalShrinking.pSeries 2 (Work.Shrinking.freeOperatorGroup G n) (j + 1) →
      z = u * p → (z ^ (2 ^ k))⁻¹ * (u ^ (2 ^ k)) ∈ Tm G n (j + k) (j + 1) := by
    intro u p z hu hp hpp hz
    have hq := addPowRefined' (P := Work.Shrinking.freeOperatorGroup G n) j k (by omega) hk hu hp
    have hp' := hpN p hpp
    rw [hz]
    rw [show ((u * p) ^ (2 ^ k))⁻¹ * (u ^ (2 ^ k))
        = (((u * p) ^ (2 ^ k))⁻¹ * (u ^ (2 ^ k) * p ^ (2 ^ k))) * (p ^ (2 ^ k))⁻¹
        from by group]
    exact Subgroup.mul_mem _ hq (Subgroup.inv_mem _ hp')
  have hstep1 := hstep u₁ p₁ z₁ hTm1 hTp1 hp₁ hu₁p₁.symm
  have hstep2 := hstep u₂ p₂ z₂ hTm2 hTp2 hp₂ hu₂p₂.symm
  -- `(u₁^(2^k))⁻¹ u₂^(2^k) ∈ N`
  have hBA : (u₁ ^ (2 ^ k))⁻¹ * (z₁ ^ (2 ^ k)) ∈ Tm G n (j + k) (j + 1) := by
    have h := Subgroup.inv_mem _ hstep1
    rwa [mul_inv_rev, inv_inv] at h
  have h4 : (u₁ ^ (2 ^ k))⁻¹ * (u₂ ^ (2 ^ k)) ∈ Tm G n (j + k) (j + 1) := by
    rw [show (u₁ ^ (2 ^ k))⁻¹ * (u₂ ^ (2 ^ k))
        = ((u₁ ^ (2 ^ k))⁻¹ * (z₁ ^ (2 ^ k))) * ((z₁ ^ (2 ^ k))⁻¹ * (z₂ ^ (2 ^ k)))
          * ((z₂ ^ (2 ^ k))⁻¹ * (u₂ ^ (2 ^ k))) from by group]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hBA heq) hstep2
  -- `(u₁⁻¹u₂)^(2^k) ∈ N`
  have h5 : (u₁⁻¹ * u₂) ^ (2 ^ k) ∈ Tm G n (j + k) (j + 1) := by
    have hq := addPowRefined' (P := Work.Shrinking.freeOperatorGroup G n) j k (by omega) hk
      (Subgroup.inv_mem _ hTm1) hTm2
    have hYX : (u₁⁻¹ * u₂) ^ (2 ^ k)
        = ((u₁ ^ (2 ^ k))⁻¹ * (u₂ ^ (2 ^ k)))
          * (((u₁⁻¹ * u₂) ^ (2 ^ k))⁻¹ * ((u₁⁻¹) ^ (2 ^ k) * (u₂ ^ (2 ^ k))))⁻¹ := by
      rw [inv_pow]
      group
    rw [hYX]
    exact Subgroup.mul_mem _ h4 (Subgroup.inv_mem _ hq)
  -- rigidity
  have h6 : u₁⁻¹ * u₂ ∈ Work.CohomologicalShrinking.pSeries 2
      (Work.Shrinking.freeOperatorGroup G n) (j + 1) :=
    Work.SSGRoute.PowRigidity.gradedStepPowMemImp (Fin n × G) j k hj hk
      (Subgroup.mul_mem _ (Subgroup.inv_mem _ hu₁) hu₂) h5
  rw [Tm_self_eq_pSeries]
  rw [hu₁p₁.symm, hu₂p₂.symm]
  rw [show (u₁ * p₁)⁻¹ * (u₂ * p₂) = p₁⁻¹ * (u₁⁻¹ * u₂) * p₂ from by group]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hp₁) h6) hp₂

/-- **Surjectivity** of the `2^k`-th power map onto the graded piece `T(j+k,j)/T(j+k,j+1)`,
from the generation statement `gen_aux`. -/
theorem surj_aux (j k : ℕ) (hj : 1 ≤ j) (hk : 1 ≤ k)
    {z : Work.Shrinking.freeOperatorGroup G n} (hz : z ∈ Tm G n (j + k) j) :
    ∃ z' ∈ Tm G n j j,
      toQ G n (j + k) (j + 1) (z' ^ (2 ^ k)) = toQ G n (j + k) (j + 1) z := by
  set S : Set (Work.Shrinking.freeOperatorGroup G n) :=
    {y | ∃ x : Fin j → Work.Shrinking.freeOperatorGroup G n,
      y = (Work.SSGRoute.prop5.commWord j x) ^ (2 ^ k)} with hS
  haveI : (Tm G n (j + k) (j + 1)).Normal :=
    Work.CohomologicalShrinking.refinedTerm_normal 2 (Work.Shrinking.freeOperatorGroup G n)
      (j + k) (j + 1)
  have hz1 : z ∈ Subgroup.closure S ⊔ Tm G n (j + k) (j + 1) := (gen_aux G n j k hj hk) hz
  obtain ⟨a, ha, b, hb, hab⟩ := (Subgroup.mem_sup_of_normal_right (t := Tm G n (j + k) (j + 1))).mp hz1
  have hmemTm : ∀ x : Fin j → Work.Shrinking.freeOperatorGroup G n,
      Work.SSGRoute.prop5.commWord j x ∈ Tm G n j j := by
    intro x
    have hc : Work.SSGRoute.prop5.commWord j x ∈ Work.CohomologicalShrinking.centralSeries
        (Work.Shrinking.freeOperatorGroup G n) j :=
      Work.SSGRoute.prop5.commWord_mem_lowerCentralSeries j x
    show Work.SSGRoute.prop5.commWord j x ∈ Tm G n j j
    rw [show Tm G n j j = Work.CohomologicalShrinking.refinedTerm 2
      (Work.Shrinking.freeOperatorGroup G n) j j from rfl,
      Work.CohomologicalShrinking.refinedTerm]
    exact Subgroup.mem_sup_left (Subgroup.mem_inf.mpr
      ⟨centralSeries_le_pSeries (P := Work.Shrinking.freeOperatorGroup G n) j hc, hc⟩)
  have key : ∀ y ∈ Subgroup.closure S,
      ∃ z' ∈ Tm G n j j, toQ G n (j + k) (j + 1) (z' ^ (2 ^ k)) = toQ G n (j + k) (j + 1) y := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
        obtain ⟨x, rfl⟩ := hy
        exact ⟨Work.SSGRoute.prop5.commWord j x, hmemTm x, rfl⟩
    | one => exact ⟨1, Subgroup.one_mem _, by rw [one_pow]⟩
    | mul y₁ y₂ hy₁ hy₂ ih₁ ih₂ =>
        obtain ⟨z₁, hz₁, he₁⟩ := ih₁
        obtain ⟨z₂, hz₂, he₂⟩ := ih₂
        rw [toQ_eq_iff] at he₁ he₂
        refine ⟨z₁ * z₂, Subgroup.mul_mem _ hz₁ hz₂, ?_⟩
        rw [toQ_eq_iff]
        have hq := addPowRefined' (P := Work.Shrinking.freeOperatorGroup G n) j k hj hk hz₁ hz₂
        rw [show ((z₁ * z₂) ^ (2 ^ k))⁻¹ * (y₁ * y₂)
            = (((z₁ * z₂) ^ (2 ^ k))⁻¹ * (z₁ ^ (2 ^ k) * z₂ ^ (2 ^ k)))
              * ((z₂ ^ (2 ^ k))⁻¹ * y₂) * (y₂⁻¹ * ((z₁ ^ (2 ^ k))⁻¹ * y₁) * y₂)
            from by group]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hq he₂)
          (Subgroup.Normal.conj_mem' (inferInstance : (Tm G n (j + k) (j + 1)).Normal)
            ((z₁ ^ (2 ^ k))⁻¹ * y₁) he₁ y₂)
    | inv y₁ hy₁ ih₁ =>
        obtain ⟨z₁, hz₁, he₁⟩ := ih₁
        rw [toQ_eq_iff] at he₁
        refine ⟨z₁⁻¹, Subgroup.inv_mem _ hz₁, ?_⟩
        rw [toQ_eq_iff]
        rw [show ((z₁⁻¹) ^ (2 ^ k))⁻¹ * y₁⁻¹
            = y₁ * (((z₁ ^ (2 ^ k))⁻¹ * y₁)⁻¹) * y₁⁻¹ from by
          rw [inv_pow, inv_inv]; group]
        exact Subgroup.Normal.conj_mem (inferInstance : (Tm G n (j + k) (j + 1)).Normal)
          (((z₁ ^ (2 ^ k))⁻¹ * y₁)⁻¹) (Subgroup.inv_mem _ he₁) y₁
  obtain ⟨z', hz', hzeq⟩ := key a ha
  refine ⟨z', hz', ?_⟩
  rw [hzeq, ← hab, map_mul, show toQ G n (j + k) (j + 1) b = 1 from ?_, mul_one]
  rw [show (1 : Qt G n (j + k) (j + 1)) = toQ G n (j + k) (j + 1) 1 from (map_one _).symm,
    toQ_eq_iff]
  simpa using Subgroup.inv_mem _ hb
theorem main_aux_at (j k : ℕ) (hj : 2 ≤ j) (hk : 1 ≤ k) (δ : G) (hδ : δ * δ = 1)
    (hdiag : ∀ c : Qt G n
        (Work.CohomologicalShrinking.tauSucc j j).1
        (Work.CohomologicalShrinking.tauSucc j j).2,
      flowQuotSucc 2 G n j j c = 1 →
      flowAction 2 G n (Work.CohomologicalShrinking.tauSucc j j).1
          (Work.CohomologicalShrinking.tauSucc j j).2 δ c = c⁻¹ →
      ∃ e : Qt G n (Work.CohomologicalShrinking.tauSucc j j).1
          (Work.CohomologicalShrinking.tauSucc j j).2,
        c = (flowAction 2 G n (Work.CohomologicalShrinking.tauSucc j j).1
              (Work.CohomologicalShrinking.tauSucc j j).2 δ e)⁻¹ * e)
    (z : Work.Shrinking.freeOperatorGroup G n) (hz : z ∈ Tm G n (j + k) j)
    (hanti : (δ • z)⁻¹ * z⁻¹ ∈ Tm G n (j + k) (j + 1)) :
    ∃ E₀ : Work.Shrinking.freeOperatorGroup G n,
      toQ G n (j + k) (j + 1) z
        = (flowAction 2 G n (j + k) (j + 1) δ
              (toQ G n (j + k) (j + 1) (E₀ ^ (2 ^ k))))⁻¹
          * (toQ G n (j + k) (j + 1) (E₀ ^ (2 ^ k))) := by
  obtain ⟨z', hz', hz'eq⟩ := surj_aux G n j k (by omega) hk hz
  -- the classes of `z'^(2^k)` and of `z` agree
  have hc : toQ G n (j + k) (j + 1) (z' ^ (2 ^ k)) = toQ G n (j + k) (j + 1) z := hz'eq
  -- `c'' = toQ z'` is in the kernel
  have hker'' : flowQuotSucc 2 G n j j
      (toQ G n (Work.CohomologicalShrinking.tauSucc j j).1
        (Work.CohomologicalShrinking.tauSucc j j).2 z') = 1 :=
    (flowQuotSucc_toQ_eq_one (G := G) (n := n) j j z').mpr hz'
  -- `c''` is anti-fixed
  have hz'2 : z' ^ 2 ∈ Tm G n (Work.CohomologicalShrinking.tauSucc j j).1
      (Work.CohomologicalShrinking.tauSucc j j).2 := by
    rw [Tm_self_eq_pSeries]
    have hP : z' ∈ Work.CohomologicalShrinking.pSeries 2
        (Work.Shrinking.freeOperatorGroup G n) j :=
      (Work.CohomologicalShrinking.refinedTerm_le_pSeries 2
        (Work.Shrinking.freeOperatorGroup G n) j j) hz'
    simpa using pow_two_pow_mem_pSeries (P := Work.Shrinking.freeOperatorGroup G n) j 1
      (by omega) hP
  have hδz' : δ • z' ∈ Tm G n j j := by
    rw [show Tm G n j j = Work.CohomologicalShrinking.refinedTerm 2
      (Work.Shrinking.freeOperatorGroup G n) j j from rfl,
      ← Work.CohomologicalShrinking.map_refinedTerm_eq 2
        (MulDistribMulAction.toMulAut G (Work.Shrinking.freeOperatorGroup G n) δ) j j]
    exact Subgroup.mem_map_of_mem _ hz'
  have hz'inv : z'⁻¹ ∈ Tm G n j j := Subgroup.inv_mem _ hz'
  -- the key input to `inj_aux`
  have hkey : ((δ • z') ^ (2 ^ k))⁻¹ * ((z'⁻¹) ^ (2 ^ k)) ∈ Tm G n (j + k) (j + 1) := by
    have hL : toQ G n (j + k) (j + 1) ((δ • z') ^ (2 ^ k))
        = toQ G n (j + k) (j + 1) (δ • z) := by
      rw [map_pow, ← gs32_toQ_smul (G := G) (n := n) (j + k) (j + 1) δ z']
      rw [← map_pow (flowAction 2 G n (j + k) (j + 1) δ)
        (toQ G n (j + k) (j + 1) z') (2 ^ k)]
      rw [← map_pow (toQ G n (j + k) (j + 1)) z' (2 ^ k), hc]
      rw [gs32_toQ_smul]
    have hR : toQ G n (j + k) (j + 1) ((z'⁻¹) ^ (2 ^ k))
        = toQ G n (j + k) (j + 1) (z⁻¹) := by
      rw [inv_pow, map_inv, hc, ← map_inv]
    have h1 : toQ G n (j + k) (j + 1) (((δ • z') ^ (2 ^ k))⁻¹ * ((z'⁻¹) ^ (2 ^ k))) = 1 := by
      rw [map_mul, map_inv]
      rw [hL, hR]
      rw [show toQ G n (j + k) (j + 1) (δ • z) = toQ G n (j + k) (j + 1) (z⁻¹) from
        (toQ_eq_iff (G := G) (n := n) (j + k) (j + 1) (δ • z) z⁻¹).mpr hanti]
      rw [inv_mul_cancel]
    have := (toQ_eq_iff (G := G) (n := n) (j + k) (j + 1) 1
      (((δ • z') ^ (2 ^ k))⁻¹ * ((z'⁻¹) ^ (2 ^ k)))).mp (by rw [map_one]; exact h1.symm)
    simpa using this
  have hinj := inj_aux G n j k hj hk hδz' hz'inv hkey
  -- `(δ • z')⁻¹ * z' ∈ T(tauSucc j j)`
  have hfix : (δ • z')⁻¹ * z' ∈ Tm G n (Work.CohomologicalShrinking.tauSucc j j).1
      (Work.CohomologicalShrinking.tauSucc j j).2 := by
    rw [show (δ • z')⁻¹ * z' = ((δ • z')⁻¹ * (z'⁻¹)) * z' ^ 2 from by group]
    exact Subgroup.mul_mem _ hinj hz'2
  have hsq : (toQ G n (Work.CohomologicalShrinking.tauSucc j j).1
      (Work.CohomologicalShrinking.tauSucc j j).2 z') *
      (toQ G n (Work.CohomologicalShrinking.tauSucc j j).1
        (Work.CohomologicalShrinking.tauSucc j j).2 z') = 1 := by
    have h2 : (toQ G n (Work.CohomologicalShrinking.tauSucc j j).1
        (Work.CohomologicalShrinking.tauSucc j j).2 z') ^ 2 = 1 := by
      rw [← map_pow,
        show (1 : Qt G n (Work.CohomologicalShrinking.tauSucc j j).1
          (Work.CohomologicalShrinking.tauSucc j j).2) =
          toQ G n (Work.CohomologicalShrinking.tauSucc j j).1
            (Work.CohomologicalShrinking.tauSucc j j).2 1 from (map_one _).symm]
      exact (toQ_eq_iff (G := G) (n := n) _ _ _ 1).mpr (by simpa using hz'2)
    rwa [pow_two] at h2
  have hanti'' : flowAction 2 G n (Work.CohomologicalShrinking.tauSucc j j).1
      (Work.CohomologicalShrinking.tauSucc j j).2 δ
      (toQ G n (Work.CohomologicalShrinking.tauSucc j j).1
        (Work.CohomologicalShrinking.tauSucc j j).2 z') =
      (toQ G n (Work.CohomologicalShrinking.tauSucc j j).1
        (Work.CohomologicalShrinking.tauSucc j j).2 z')⁻¹ := by
    rw [gs32_toQ_smul]
    have h1 : toQ G n (Work.CohomologicalShrinking.tauSucc j j).1
        (Work.CohomologicalShrinking.tauSucc j j).2 (δ • z') =
        toQ G n (Work.CohomologicalShrinking.tauSucc j j).1
        (Work.CohomologicalShrinking.tauSucc j j).2 z' :=
      (toQ_eq_iff (G := G) (n := n) _ _ _ _).mpr hfix
    rw [h1]
    exact (inv_eq_of_mul_eq_one_right hsq).symm
  -- the diagonal hypothesis
  obtain ⟨e', he'⟩ := hdiag _ hker'' hanti''
  -- a lift of `e'`
  obtain ⟨E₀, hE₀⟩ : ∃ E₀ : Work.Shrinking.freeOperatorGroup G n,
      toQ G n (Work.CohomologicalShrinking.tauSucc j j).1
        (Work.CohomologicalShrinking.tauSucc j j).2 E₀ = e' := by
    obtain ⟨Z, hZ⟩ := QuotientGroup.mk'_surjective
      ((Tm G n (Work.CohomologicalShrinking.tauSucc j j).1
        (Work.CohomologicalShrinking.tauSucc j j).2).subgroupOf ⊤) e'
    refine ⟨Z.1, ?_⟩
    show (QuotientGroup.mk' ((Tm G n (Work.CohomologicalShrinking.tauSucc j j).1
      (Work.CohomologicalShrinking.tauSucc j j).2).subgroupOf ⊤))
      (Subgroup.topEquiv.symm.toMonoidHom Z.1) = e'
    rw [show Subgroup.topEquiv.symm.toMonoidHom Z.1 = Z from Subtype.ext rfl]
    exact hZ
  refine ⟨E₀, ?_⟩
  -- `C' = (δE₀)⁻¹ E₀` has the class of `z'`
  set X : Work.Shrinking.freeOperatorGroup G n := δ • E₀ with hX
  set C' : Work.Shrinking.freeOperatorGroup G n := X⁻¹ * E₀ with hC'
  have hE₀eq : E₀ = X * C' := by rw [hC']; group
  have hC'_cls : toQ G n (Work.CohomologicalShrinking.tauSucc j j).1
      (Work.CohomologicalShrinking.tauSucc j j).2 C' =
      toQ G n (Work.CohomologicalShrinking.tauSucc j j).1
        (Work.CohomologicalShrinking.tauSucc j j).2 z' := by
    have h1 : toQ G n (Work.CohomologicalShrinking.tauSucc j j).1
        (Work.CohomologicalShrinking.tauSucc j j).2 C'
        = (flowAction 2 G n (Work.CohomologicalShrinking.tauSucc j j).1
            (Work.CohomologicalShrinking.tauSucc j j).2 δ e')⁻¹ * e' := by
      rw [hC', hX, map_mul, map_inv,
        ← gs32_toQ_smul (G := G) (n := n) (Work.CohomologicalShrinking.tauSucc j j).1
          (Work.CohomologicalShrinking.tauSucc j j).2 δ E₀, hE₀]
    rw [h1, ← he']
  -- hence `C' ∈ T(j,j)` and `z' = C' * p` with `p ∈ P_{j+1}`
  have hpp' : z'⁻¹ * C' ∈ Work.CohomologicalShrinking.pSeries 2
      (Work.Shrinking.freeOperatorGroup G n) (j + 1) := by
    have h := Subgroup.inv_mem _ ((toQ_eq_iff (G := G) (n := n)
      (Work.CohomologicalShrinking.tauSucc j j).1
      (Work.CohomologicalShrinking.tauSucc j j).2 C' z').mp hC'_cls)
    rw [mul_inv_rev, inv_inv] at h
    rwa [Tm_self_eq_pSeries] at h
  have hC'Tm' : C' ∈ Tm G n j j := by
    have hmem : z'⁻¹ * C' ∈ Tm G n j j := by
      rw [Tm_jj_eq]
      exact Subgroup.mem_sup_right hpp'
    rw [show C' = z' * (z'⁻¹ * C') from by group]
    exact Subgroup.mul_mem _ hz' hmem
  set p : Work.Shrinking.freeOperatorGroup G n := (C')⁻¹ * z' with hpdef
  have hp : p ∈ Work.CohomologicalShrinking.pSeries 2
      (Work.Shrinking.freeOperatorGroup G n) (j + 1) := by
    have h := (toQ_eq_iff (G := G) (n := n)
      (Work.CohomologicalShrinking.tauSucc j j).1
      (Work.CohomologicalShrinking.tauSucc j j).2 C' z').mp hC'_cls
    rw [Tm_self_eq_pSeries] at h
    exact h
  have hzp : z' = C' * p := by rw [hpdef]; group
  -- **(g)** the verification
  rw [show toQ G n (j + k) (j + 1) z
      = toQ G n (j + k) (j + 1) (((δ • E₀) ^ (2 ^ k))⁻¹ * (E₀ ^ (2 ^ k))) from ?_]
  · rw [map_mul, map_inv,
      show (δ • E₀) ^ (2 ^ k) = δ • (E₀ ^ (2 ^ k)) from
        (map_pow (MulDistribMulAction.toMulAut G (Work.Shrinking.freeOperatorGroup G n) δ)
          E₀ (2 ^ k)).symm]
    rw [← gs32_toQ_smul (G := G) (n := n) (j + k) (j + 1) δ (E₀ ^ (2 ^ k))]
  · rw [toQ_eq_iff]
    have hN : (Tm G n (j + k) (j + 1)).Normal :=
      Work.CohomologicalShrinking.refinedTerm_normal 2
        (Work.Shrinking.freeOperatorGroup G n) (j + k) (j + 1)
    -- the transfer lemma on `(X, C')`
    have htr1 := transferPowGeneral
      (Work.Shrinking.freeOperatorGroup G n) 1 1 j j k (le_refl 1) (by omega) hk
      (by rw [Work.CohomologicalShrinking.refinedTerm_one,
        Work.CohomologicalShrinking.pSeries_one]; exact Subgroup.mem_top X) hC'Tm'
    -- `D · (C'^(2^k))⁻¹ ∈ T(j+k,j+1)`, where `D = ((δ•E₀)^(2^k))⁻¹ * E₀^(2^k)`
    have hA : (((δ • E₀) ^ (2 ^ k))⁻¹ * (E₀ ^ (2 ^ k))) * (C' ^ (2 ^ k))⁻¹ ∈
        Tm G n (j + k) (j + 1) := by
      rw [show (δ • E₀) = X from hX.symm, hE₀eq]
      exact refinedTerm_mono 2 (Work.Shrinking.freeOperatorGroup G n)
        (by omega) (by omega) htr1
    -- `C'^(2^k) ≡ z'^(2^k)` and `z'^(2^k) ≡ z`
    have h2 : (C' ^ (2 ^ k))⁻¹ * (z' ^ (2 ^ k)) ∈ Tm G n (j + k) (j + 1) := by
      have htr2 := transferPowGeneral
        (Work.Shrinking.freeOperatorGroup G n) j j (j + 1) 1 k (by omega) (by omega) hk
        hC'Tm' (by
          rw [Work.CohomologicalShrinking.refinedTerm_one]
          exact hp)
      have hpk : p ^ (2 ^ k) ∈ Tm G n (j + k) (j + 1) := by
        rw [show Tm G n (j + k) (j + 1) = Work.CohomologicalShrinking.refinedTerm 2
          (Work.Shrinking.freeOperatorGroup G n) (j + k) (j + 1) from rfl,
          Work.CohomologicalShrinking.refinedTerm]
        refine Subgroup.mem_sup_right ?_
        exact Work.CohomologicalShrinking.pSeries_antitone 2
          (Work.Shrinking.freeOperatorGroup G n) (by omega)
          (pow_two_pow_mem_pSeries (j + 1) k (by omega) hp)
      rw [hzp]
      rw [show (C' ^ (2 ^ k))⁻¹ * (C' * p) ^ (2 ^ k)
          = ((C' ^ (2 ^ k))⁻¹ * (C' * p) ^ (2 ^ k) * (p ^ (2 ^ k))⁻¹) * p ^ (2 ^ k)
          from by group]
      exact Subgroup.mul_mem _
        (refinedTerm_mono 2 (Work.Shrinking.freeOperatorGroup G n)
          (by omega) (by omega) htr2) hpk
    have h3 : (z' ^ (2 ^ k))⁻¹ * z ∈ Tm G n (j + k) (j + 1) :=
      (toQ_eq_iff _ _ _ _).mp hz'eq
    have hB : (C' ^ (2 ^ k)) * (z' ^ (2 ^ k))⁻¹ ∈ Tm G n (j + k) (j + 1) :=
      (mul_inv_mem_iff_inv_mul_mem hN).mpr h2
    have hC : (z' ^ (2 ^ k)) * z⁻¹ ∈ Tm G n (j + k) (j + 1) :=
      (mul_inv_mem_iff_inv_mul_mem hN).mpr h3
    have hDz : (((δ • E₀) ^ (2 ^ k))⁻¹ * (E₀ ^ (2 ^ k))) * z⁻¹ ∈ Tm G n (j + k) (j + 1) := by
      rw [show (((δ • E₀) ^ (2 ^ k))⁻¹ * (E₀ ^ (2 ^ k))) * z⁻¹
          = ((((δ • E₀) ^ (2 ^ k))⁻¹ * (E₀ ^ (2 ^ k))) * (C' ^ (2 ^ k))⁻¹)
            * ((C' ^ (2 ^ k)) * (z' ^ (2 ^ k))⁻¹) * ((z' ^ (2 ^ k)) * z⁻¹) from by group]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hA hB) hC
    rw [show z⁻¹ * (((δ • E₀) ^ (2 ^ k))⁻¹ * (E₀ ^ (2 ^ k)))
        = z⁻¹ * ((((δ • E₀) ^ (2 ^ k))⁻¹ * (E₀ ^ (2 ^ k))) * z⁻¹) * z from by group]
    exact Subgroup.Normal.conj_mem' hN _ hDz z
end Main

/-- **The `j ≥ 2` graded step from its single diagonal instance.**  For a fixed `j ≥ 2`,
if the diagonal instance `(j,j)` of the graded step holds (every anti-fixed element of the
graded piece `E(j,j) = ker(Q_{(j+1,1)} → Q_{(j,j)})` is a `δ`-difference in `Q_{(j+1,1)}`),
then so does every pair `(i,j)` with `i ≥ j`. -/
theorem gradedStep_of_diagonal_at (G : Type*) [Group G] [Fintype G] (n : ℕ) (δ : G)
    (hδ : δ * δ = 1) (hδ1 : δ ≠ 1) (j : ℕ) (hj : 2 ≤ j)
    (hdiag : ∀ c : Work.CohomologicalShrinking.flowQuotient 2 G n
        (Work.CohomologicalShrinking.tauSucc j j).1
        (Work.CohomologicalShrinking.tauSucc j j).2,
      Work.SSGRoute.flowQuotSucc 2 G n j j c = 1 →
      Work.CohomologicalShrinking.flowAction 2 G n
          (Work.CohomologicalShrinking.tauSucc j j).1
          (Work.CohomologicalShrinking.tauSucc j j).2 δ c = c⁻¹ →
      ∃ e : Work.CohomologicalShrinking.flowQuotient 2 G n
            (Work.CohomologicalShrinking.tauSucc j j).1
            (Work.CohomologicalShrinking.tauSucc j j).2,
        c = (Work.CohomologicalShrinking.flowAction 2 G n
              (Work.CohomologicalShrinking.tauSucc j j).1
              (Work.CohomologicalShrinking.tauSucc j j).2 δ e)⁻¹ * e)
    :
    ∀ (i : ℕ), j ≤ i →
      ∀ c : Work.CohomologicalShrinking.flowQuotient 2 G n
          (Work.CohomologicalShrinking.tauSucc i j).1
          (Work.CohomologicalShrinking.tauSucc i j).2,
        Work.SSGRoute.flowQuotSucc 2 G n i j c = 1 →
        Work.CohomologicalShrinking.flowAction 2 G n
            (Work.CohomologicalShrinking.tauSucc i j).1
            (Work.CohomologicalShrinking.tauSucc i j).2 δ c = c⁻¹ →
        ∃ e : Work.CohomologicalShrinking.flowQuotient 2 G n
              (Work.CohomologicalShrinking.tauSucc i j).1
              (Work.CohomologicalShrinking.tauSucc i j).2,
          c = (Work.CohomologicalShrinking.flowAction 2 G n
                (Work.CohomologicalShrinking.tauSucc i j).1
                (Work.CohomologicalShrinking.tauSucc i j).2 δ e)⁻¹ * e := by
  intro i hji c hker hanti
  rcases eq_or_lt_of_le hji with h | h
  · subst h
    exact hdiag c hker hanti
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (le_of_lt h)
    have hk1 : 1 ≤ k := by omega
    have hTmeq : Tm G n (Work.CohomologicalShrinking.tauSucc (j + k) j).1
        (Work.CohomologicalShrinking.tauSucc (j + k) j).2 = Tm G n (j + k) (j + 1) :=
      Tm_tauSucc_of_lt (G := G) (n := n) (i := j + k) (j := j) (by omega)
    obtain ⟨Z, hZ⟩ := QuotientGroup.mk'_surjective
      ((Tm G n (Work.CohomologicalShrinking.tauSucc (j + k) j).1
        (Work.CohomologicalShrinking.tauSucc (j + k) j).2).subgroupOf ⊤) c
    have hzc : toQ G n (Work.CohomologicalShrinking.tauSucc (j + k) j).1
        (Work.CohomologicalShrinking.tauSucc (j + k) j).2 Z.1 = c := by
      show (QuotientGroup.mk' ((Tm G n (Work.CohomologicalShrinking.tauSucc (j + k) j).1
        (Work.CohomologicalShrinking.tauSucc (j + k) j).2).subgroupOf ⊤))
        (Subgroup.topEquiv.symm.toMonoidHom Z.1) = c
      rw [show Subgroup.topEquiv.symm.toMonoidHom Z.1 = Z from Subtype.ext rfl]
      exact hZ
    have hz : Z.1 ∈ Tm G n (j + k) j :=
      (flowQuotSucc_toQ_eq_one (G := G) (n := n) (j + k) j Z.1).mp (by rw [hzc]; exact hker)
    have hanti' : (δ • Z.1)⁻¹ * Z.1⁻¹ ∈ Tm G n (j + k) (j + 1) := by
      have h1 : toQ G n (Work.CohomologicalShrinking.tauSucc (j + k) j).1
            (Work.CohomologicalShrinking.tauSucc (j + k) j).2 (δ • Z.1)
          = toQ G n (Work.CohomologicalShrinking.tauSucc (j + k) j).1
            (Work.CohomologicalShrinking.tauSucc (j + k) j).2 (Z.1⁻¹) := by
        rw [← gs32_toQ_smul (G := G) (n := n)
            (Work.CohomologicalShrinking.tauSucc (j + k) j).1
            (Work.CohomologicalShrinking.tauSucc (j + k) j).2 δ Z.1,
          hzc, hanti, map_inv, hzc]
      have h2 := (toQ_eq_iff (G := G) (n := n)
        (Work.CohomologicalShrinking.tauSucc (j + k) j).1
        (Work.CohomologicalShrinking.tauSucc (j + k) j).2 (δ • Z.1) (Z.1⁻¹)).mp h1
      rwa [hTmeq] at h2
    obtain ⟨E₀, hE₀⟩ := main_aux_at G n j k hj hk1 δ hδ hdiag Z.1 hz hanti'
    refine ⟨toQ G n (Work.CohomologicalShrinking.tauSucc (j + k) j).1
      (Work.CohomologicalShrinking.tauSucc (j + k) j).2 (E₀ ^ (2 ^ k)), ?_⟩
    rw [← hzc,
      gs32_toQ_smul (G := G) (n := n) (Work.CohomologicalShrinking.tauSucc (j + k) j).1
        (Work.CohomologicalShrinking.tauSucc (j + k) j).2 δ (E₀ ^ (2 ^ k)),
      ← map_inv, ← map_mul, toQ_eq_iff, hTmeq]
    rw [gs32_toQ_smul (G := G) (n := n) (j + k) (j + 1) δ (E₀ ^ (2 ^ k)), ← map_inv,
      ← map_mul, toQ_eq_iff] at hE₀
    exact hE₀


end RedDiag

open RedDiag

/-- **The `(3,2)` graded step at `p = 2` in the reduced cone.**  For an arbitrary finite group `G`
and an involution `δ ≠ 1`, every `δ`-anti-fixed element of the graded piece
`E(3,2) = ker(Q_{(3,3)} → Q_{(3,2)})` is a `δ`-difference in the ambient group `Q_{(3,3)}`. -/
theorem gradedStep_three_two_reduced (G : Type*) [Group G] [Fintype G] (n : ℕ) (δ : G)
    (hδ : δ * δ = 1) (hδ1 : δ ≠ 1) :
    ∀ c : Work.CohomologicalShrinking.flowQuotient 2 G n
        (Work.CohomologicalShrinking.tauSucc 3 2).1
        (Work.CohomologicalShrinking.tauSucc 3 2).2,
      Work.SSGRoute.flowQuotSucc 2 G n 3 2 c = 1 →
      Work.CohomologicalShrinking.flowAction 2 G n
          (Work.CohomologicalShrinking.tauSucc 3 2).1
          (Work.CohomologicalShrinking.tauSucc 3 2).2 δ c = c⁻¹ →
      ∃ e : Work.CohomologicalShrinking.flowQuotient 2 G n
            (Work.CohomologicalShrinking.tauSucc 3 2).1
            (Work.CohomologicalShrinking.tauSucc 3 2).2,
        c = (Work.CohomologicalShrinking.flowAction 2 G n
              (Work.CohomologicalShrinking.tauSucc 3 2).1
              (Work.CohomologicalShrinking.tauSucc 3 2).2 δ e)⁻¹ * e :=
  RedDiag.gradedStep_of_diagonal_at G n δ hδ hδ1 2 (by norm_num)
    (Work.SSGRoute.LNS3A.two_two_graded_step (G := G) (n := n) (δ := δ) hδ hδ1) 3 (by norm_num)

end Work.SSGRoute
