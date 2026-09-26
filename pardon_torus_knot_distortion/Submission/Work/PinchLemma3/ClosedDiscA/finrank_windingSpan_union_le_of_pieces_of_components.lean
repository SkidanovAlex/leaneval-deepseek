import Mathlib
import Submission.Work.SurgeryInvariance.Defs
import Submission.Work.PinchLemma3.ClosedDiscA.exists_ne_zero_inf_span_le_of_intersection_three_pieces
import Submission.Work.PinchLemma3.ClosedDiscA.potential_helpers
import Submission.Work.PinchLemma3.ClosedDiscA.exists_alternating_partition
import Submission.Work.PinchLemma3.ClosedDiscA.exists_ne_zero_inf_span_le_of_intersection_pair_general
import Submission.Work.PinchLemma3.ClosedDiscA.windingSpan_union_le_sup_of_isPathConnected_inter

/-!
# The finrank bound for the winding span of the union of two inessential regions

`Work.PinchLemma3.ClosedDiscA.finrank_windingSpan_union_le_of_pieces_of_components`.

Let `A`, `B` be regions of the torus `F = P.carrier`, open in the carrier, with vanishing winding
span, and with `A` path connected.  Suppose `B` is the disjoint union of carrier-open path connected
regions `Bc s` (`s : σ`), and that `A ∩ B` is the disjoint union of carrier-open path connected
pieces `K i` (`i : ι`), each `K i` lying in `Bc (p i)` for a surjection `p : ι → σ`.  Then

  `finrank W(A ∪ B) ≤ |ι| - |σ|`.

The point is that the components of `B` *organise* the pieces of `A ∩ B`: the pair `(A, Bc s)` has
intersection `⋃_{p i = s} K i`, so adding the component `Bc s` to `A` costs at most `m s - 1`
dimensions, where `m s = #{i | p i = s}`.  Since every closed curve of `A ∪ B` is connected and
both regions are open in the carrier, and since the `Bc s` are pairwise disjoint,

  `A ∪ B = ⋃_s (A ∪ Bc s)`,

with `(A ∪ Bc_{s}) ∩ (A ∪ ⋃_{s' ∈ T} Bc_{s'}) = A` for `s ∉ T`: the incremental intersections of the
cover `(A ∪ Bc s)_s` are all the path connected set `A`, so the `1`-piece subadditivity of the
winding span (`windingSpan_union_le_sup_of_isPathConnected_inter`) can be applied one component at a
time, and the finranks add.

The individual component bounds are
* `m s = 1`: `A ∩ Bc s` is a single piece, so the intersection is path connected and
  `W(A ∪ Bc s) ≤ W(A) ⊔ W(Bc s) = ⊥`;
* `m s = 2`: the two-piece rank bound `exists_ne_zero_inf_span_le_of_intersection_pair_general`
  gives a line whose multiples of `W(A ∪ Bc s)` already lie in `W(A) ⊔ W(Bc s) = ⊥`, whence
  `finrank W(A ∪ Bc s) ≤ 1`;
* `m s ≥ 3`: `finrank W(A ∪ Bc s) ≤ finrank (ℚ × ℚ) = 2 ≤ m s - 1`.
-/

open LeanEval.KnotTheory.PardonDistortion Set

namespace Work.PinchLemma3.ClosedDiscA

noncomputable section

-- `hBop` and `hBc_pc` are part of the requested interface but are not needed by the argument.
set_option linter.unusedVariables false

/-- **Linear algebra of `ℚ²`.**  If the only multiples of a nonzero vector `v` lying in `W` are zero,
then `W` has dimension at most one. -/
theorem finrank_le_one_of_inf_span_le_bot {W : Submodule ℚ (ℚ × ℚ)} {v : ℚ × ℚ}
    (hv : v ≠ 0) (h : W ⊓ Submodule.span ℚ ({v} : Set (ℚ × ℚ)) ≤ ⊥) :
    Module.finrank ℚ ↥W ≤ 1 := by
  have hv1 : Module.finrank ℚ ↥(Submodule.span ℚ ({v} : Set (ℚ × ℚ))) = 1 :=
    finrank_span_singleton hv
  have hbot : W ⊓ Submodule.span ℚ ({v} : Set (ℚ × ℚ)) = ⊥ := le_bot_iff.mp h
  have hfr := Submodule.finrank_sup_add_finrank_inf_eq W (Submodule.span ℚ ({v} : Set (ℚ × ℚ)))
  rw [hbot, finrank_bot, hv1] at hfr
  have hle : Module.finrank ℚ ↥(W ⊔ Submodule.span ℚ ({v} : Set (ℚ × ℚ))) ≤ 2 := by
    have h2 := Submodule.finrank_mono (le_top : W ⊔ Submodule.span ℚ ({v} : Set (ℚ × ℚ)) ≤ ⊤)
    rwa [finrank_top, Module.finrank_prod, Module.finrank_self] at h2
  omega

theorem finrank_windingSpan_union_le_of_pieces_of_components
    {P : Work.CoreTopology.ParamTorus}
    {A B : Set LeanEval.KnotTheory.PardonDistortion.R3}
    (hAc : A ⊆ P.carrier) (hBc : B ⊆ P.carrier)
    (hAop : Work.SurgeryInvariance.IsOpenInCarrier P A)
    (hBop : Work.SurgeryInvariance.IsOpenInCarrier P B)
    (hApc : IsPathConnected A)
    (hVA : Work.SurgeryInvariance.WindingSpan P A = ⊥)
    (hVB : Work.SurgeryInvariance.WindingSpan P B = ⊥)
    {σ : Type} [Fintype σ]
    (Bc : σ → Set LeanEval.KnotTheory.PardonDistortion.R3)
    (hBc_op : ∀ s, Work.SurgeryInvariance.IsOpenInCarrier P (Bc s))
    (hBc_pc : ∀ s, IsPathConnected (Bc s))
    (hBc_disj : ∀ s s', s ≠ s' → Disjoint (Bc s) (Bc s'))
    (hBsplit : B = ⋃ s, Bc s)
    {ι : Type} [Fintype ι]
    (K : ι → Set LeanEval.KnotTheory.PardonDistortion.R3)
    (hKop : ∀ i, Work.SurgeryInvariance.IsOpenInCarrier P (K i))
    (hKpc : ∀ i, IsPathConnected (K i))
    (hKdisj : ∀ i i', i ≠ i' → Disjoint (K i) (K i'))
    (hinter : A ∩ B = ⋃ i, K i)
    (p : ι → σ) (hpsurj : Function.Surjective p) (hp : ∀ i, K i ⊆ Bc (p i)) :
    Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P (A ∪ B)) ≤
      Fintype.card ι - Fintype.card σ := by
  classical
  -- ## Elementary consequences of the hypotheses
  have hBc_sub : ∀ s, Bc s ⊆ P.carrier := by
    intro s x hx
    exact hBc (by rw [hBsplit]; exact Set.mem_iUnion.mpr ⟨s, hx⟩)
  have hBcB : ∀ s, Bc s ⊆ B := by
    intro s x hx
    rw [hBsplit]; exact Set.mem_iUnion.mpr ⟨s, hx⟩
  have hVBc : ∀ s, Work.SurgeryInvariance.WindingSpan P (Bc s) = ⊥ := by
    intro s
    exact le_bot_iff.mp (le_trans (Work.SurgeryInvariance.WindingSpan_mono P (hBcB s))
      (le_of_eq hVB))
  have hKsub : ∀ i, K i ⊆ P.carrier := by
    intro i x hx
    have hxAB : x ∈ A ∩ B := by rw [hinter]; exact Set.mem_iUnion.mpr ⟨i, hx⟩
    exact hAc hxAB.1
  have hBTopen : ∀ T : Finset σ,
      Work.SurgeryInvariance.IsOpenInCarrier P (⋃ s ∈ T, Bc s) := by
    intro T
    simp only [Work.SurgeryInvariance.IsOpenInCarrier]
    have hEq : (Subtype.val ⁻¹' (⋃ s ∈ T, Bc s) : Set P.carrier)
        = ⋃ s ∈ (T : Set σ), (Subtype.val ⁻¹' Bc s) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_iUnion, Finset.mem_coe]
    rw [hEq]
    exact isOpen_biUnion (fun s _ => hBc_op s)
  have hBTsub : ∀ T : Finset σ, (⋃ s ∈ T, Bc s) ⊆ P.carrier := by
    intro T x hx
    obtain ⟨s, _, hxs⟩ := Set.mem_iUnion₂.mp hx
    exact hBc_sub s hxs
  -- ## The pieces of `A ∩ Bc s`
  have hinter_s : ∀ s : σ, A ∩ Bc s = ⋃ i : {i : ι // p i = s}, K (i : ι) := by
    intro s
    ext x
    constructor
    · rintro ⟨hxA, hxBc⟩
      have hxB : x ∈ B := by rw [hBsplit]; exact Set.mem_iUnion.mpr ⟨s, hxBc⟩
      have hxU : x ∈ ⋃ i, K i := by rw [← hinter]; exact ⟨hxA, hxB⟩
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hxU
      have hpi : p i = s := by
        by_contra hne
        exact Set.disjoint_left.mp (hBc_disj (p i) s hne) (hp i hi) hxBc
      exact Set.mem_iUnion.mpr ⟨⟨i, hpi⟩, hi⟩
    · intro hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      have hxAB : x ∈ A ∩ B := by
        rw [hinter]; exact Set.mem_iUnion.mpr ⟨(i : ι), hi⟩
      exact ⟨hxAB.1, i.2 ▸ hp (i : ι) hi⟩
  -- ## The componentwise bound
  have hcomp : ∀ s : σ,
      Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P (A ∪ Bc s))
        ≤ (Fintype.card {i : ι // p i = s}) - 1 := by
    intro s
    have hms1 : 1 ≤ Fintype.card {i : ι // p i = s} := by
      obtain ⟨i, hi⟩ := hpsurj s
      exact Fintype.card_pos_iff.mpr ⟨⟨i, hi⟩⟩
    rcases lt_or_ge (Fintype.card {i : ι // p i = s}) 2 with h2 | h2
    · -- exactly one piece
      have hcard : Fintype.card {i : ι // p i = s} = 1 := by omega
      obtain ⟨x, hx⟩ := Fintype.card_eq_one_iff.mp hcard
      have hset : (⋃ i : {i : ι // p i = s}, K (i : ι)) = K (x : ι) := by
        apply Set.Subset.antisymm
        · intro y hy
          obtain ⟨c, hc⟩ := Set.mem_iUnion.mp hy
          have hcx : (c : ι) = (x : ι) := congrArg Subtype.val (hx c)
          rwa [hcx] at hc
        · intro y hy
          exact Set.mem_iUnion.mpr ⟨x, hy⟩
      have hinter' : A ∩ Bc s = K (x : ι) := (hinter_s s).trans hset
      have hone : (Fintype.card {i : ι // p i = s}) - 1 = 0 := by omega
      rw [hone]
      have hle : Work.SurgeryInvariance.WindingSpan P (A ∪ Bc s) ≤ ⊥ := by
        have h := windingSpan_union_le_sup_of_isPathConnected_inter (P := P)
          (A := A) (B := Bc s) hAc (hBc_sub s) hAop (hBc_op s) (hinter' ▸ hKpc x)
        rw [hVA, hVBc s, sup_bot_eq] at h
        exact h
      rw [le_bot_iff.mp hle, finrank_bot]
    · rcases lt_or_ge (Fintype.card {i : ι // p i = s}) 3 with h3 | h3
      · -- exactly two pieces
        have hcard : Fintype.card {i : ι // p i = s} = 2 := by omega
        have hc2 : (Finset.univ : Finset {i : ι // p i = s}).card = 2 := by
          rw [Finset.card_univ]; exact hcard
        obtain ⟨i1, i2, hne, huniv⟩ := Finset.card_eq_two.mp hc2
        have hset : (⋃ i : {i : ι // p i = s}, K (i : ι)) = K (i1 : ι) ∪ K (i2 : ι) := by
          apply Set.Subset.antisymm
          · intro y hy
            obtain ⟨c, hc⟩ := Set.mem_iUnion.mp hy
            have hmem : c ∈ ({i1, i2} : Finset {i : ι // p i = s}) := by
              rw [← huniv]; exact Finset.mem_univ c
            simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
            rcases hmem with h | h
            · exact Or.inl (h ▸ hc)
            · exact Or.inr (h ▸ hc)
          · intro y hy
            rcases hy with hy | hy
            · exact Set.mem_iUnion.mpr ⟨i1, hy⟩
            · exact Set.mem_iUnion.mpr ⟨i2, hy⟩
        have hinter' : A ∩ Bc s = K (i1 : ι) ∪ K (i2 : ι) := (hinter_s s).trans hset
        obtain ⟨v, hvne, hvle⟩ :=
          exists_ne_zero_inf_span_le_of_intersection_pair_general
            (P := P) (A := A) (B := Bc s)
            hAc (hBc_sub s) hAop (hBc_op s) hVA (hVBc s)
            (hKsub i1) (hKsub i2) (hKop i1) (hKop i2) (hKpc i1) (hKpc i2)
            (hKdisj i1 i2 (fun h => hne (Subtype.ext h))) hinter'
        have hone : (Fintype.card {i : ι // p i = s}) - 1 = 1 := by omega
        rw [hone]
        refine finrank_le_one_of_inf_span_le_bot hvne ?_
        rw [hVA, hVBc s, sup_bot_eq] at hvle
        exact hvle
      · -- at least three pieces
        have hdim : Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P (A ∪ Bc s)) ≤ 2 := by
          have h2' := Submodule.finrank_le (Work.SurgeryInvariance.WindingSpan P (A ∪ Bc s))
          rwa [Module.finrank_prod, Module.finrank_self] at h2'
        have hge : 2 ≤ (Fintype.card {i : ι // p i = s}) - 1 := by omega
        omega
  -- ## Assembling the components one at a time
  have key : ∀ T : Finset σ,
      Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P (A ∪ ⋃ s ∈ T, Bc s))
        ≤ ∑ s ∈ T, ((Fintype.card {i : ι // p i = s}) - 1) := by
    intro T
    induction T using Finset.induction_on with
    | empty =>
        have hset : (⋃ s ∈ (∅ : Finset σ), Bc s) = (∅ : Set R3) := by simp
        rw [hset, Set.union_empty, hVA, finrank_bot]
        simp
    | insert s₀ T hs ih =>
        have hset : (⋃ s ∈ insert s₀ T, Bc s) = Bc s₀ ∪ ⋃ s ∈ T, Bc s := by
          ext x; simp [Finset.mem_insert]
        rw [hset]
        set Z : Set R3 := A ∪ Bc s₀ with hZ
        set Yu : Set R3 := A ∪ ⋃ s ∈ T, Bc s with hYu
        have hgoal : A ∪ (Bc s₀ ∪ ⋃ s ∈ T, Bc s) = Z ∪ Yu := by
          rw [hZ, hYu]
          ext x; simp only [Set.mem_union]; tauto
        rw [hgoal]
        have hZc : Z ⊆ P.carrier :=
          Set.union_subset hAc (hBc_sub s₀)
        have hYc : Yu ⊆ P.carrier :=
          Set.union_subset hAc (hBTsub T)
        have hZop : Work.SurgeryInvariance.IsOpenInCarrier P Z :=
          Work.SurgeryInvariance.isOpenInCarrier_union P hAop (hBc_op s₀)
        have hYop : Work.SurgeryInvariance.IsOpenInCarrier P Yu :=
          Work.SurgeryInvariance.isOpenInCarrier_union P hAop (hBTopen T)
        have hZnY : Z ∩ Yu = A := by
          ext x
          constructor
          · rintro ⟨hxZ, hxY⟩
            rw [hZ] at hxZ
            rw [hYu] at hxY
            rcases hxZ with hxA | hxBc
            · exact hxA
            · rcases hxY with hxA | hxU
              · exact hxA
              · exfalso
                obtain ⟨s, hsT, hxs⟩ := Set.mem_iUnion₂.mp hxU
                exact Set.disjoint_left.mp (hBc_disj s₀ s (fun h => hs (h ▸ hsT))) hxBc hxs
          · intro hxA
            exact ⟨Or.inl hxA, Or.inl hxA⟩
        have hconn : IsPathConnected (Z ∩ Yu) := hZnY ▸ hApc
        have hL1 := windingSpan_union_le_sup_of_isPathConnected_inter (P := P)
          (A := Z) (B := Yu) hZc hYc hZop hYop hconn
        have ihZ : Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P Z)
            ≤ (Fintype.card {i : ι // p i = s₀}) - 1 := by
          rw [hZ]; exact hcomp s₀
        have ihY : Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P Yu)
            ≤ ∑ s ∈ T, ((Fintype.card {i : ι // p i = s}) - 1) := by
          rw [hYu]; exact ih
        calc Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P (Z ∪ Yu))
            ≤ Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P Z ⊔
                Work.SurgeryInvariance.WindingSpan P Yu) := Submodule.finrank_mono hL1
          _ ≤ Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P Z)
                + Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan P Yu) :=
              Submodule.finrank_add_le_finrank_add_finrank _ _
          _ ≤ ((Fintype.card {i : ι // p i = s₀}) - 1)
                + ∑ s ∈ T, ((Fintype.card {i : ι // p i = s}) - 1) :=
              add_le_add ihZ ihY
          _ = ∑ s ∈ insert s₀ T, ((Fintype.card {i : ι // p i = s}) - 1) := by
              rw [Finset.sum_insert hs]
  -- ## The two index sets have the right cardinalities
  have hU : (⋃ s ∈ (Finset.univ : Finset σ), Bc s) = B := by
    rw [hBsplit]
    ext x
    simp only [Set.mem_iUnion, Finset.mem_univ, exists_true_left]
  have hge : ∀ s : σ, 1 ≤ Fintype.card {i : ι // p i = s} := by
    intro s
    obtain ⟨i, hi⟩ := hpsurj s
    exact Fintype.card_pos_iff.mpr ⟨⟨i, hi⟩⟩
  have htotal : ∑ s : σ, Fintype.card {i : ι // p i = s} = Fintype.card ι := by
    rw [← Finset.card_univ (α := ι)]
    rw [Finset.card_eq_sum_card_fiberwise (f := p) (s := Finset.univ) (t := Finset.univ)
      (fun x _ => Finset.mem_univ _)]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    rw [Fintype.card_subtype]
  have hdecomp : ∑ s : σ, ((Fintype.card {i : ι // p i = s}) - 1) + Fintype.card σ
      = ∑ s : σ, Fintype.card {i : ι // p i = s} := by
    rw [show (Fintype.card σ : ℕ) = ∑ _s : σ, 1 from by simp,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun s _ => ?_)
    have := hge s
    omega
  have hsum : ∑ s ∈ (Finset.univ : Finset σ), ((Fintype.card {i : ι // p i = s}) - 1)
      = Fintype.card ι - Fintype.card σ := by
    have hsub : ∑ s : σ, ((Fintype.card {i : ι // p i = s}) - 1)
        = ∑ s : σ, Fintype.card {i : ι // p i = s} - Fintype.card σ :=
      Nat.eq_sub_of_add_eq hdecomp
    rw [hsub, htotal]
  have hfin := key Finset.univ
  rw [hU, hsum] at hfin
  exact hfin

end

end Work.PinchLemma3.ClosedDiscA
