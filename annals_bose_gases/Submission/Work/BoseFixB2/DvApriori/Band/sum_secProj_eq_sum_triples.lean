import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB2.DvApriori.Band.Support
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB2.DvApriori.Band.sum_secProj_eq_sum_triples`

FS §6 band analysis: the `n₊`-graded off-diagonal pairing of the potential part of the
box word.  Writing `E_S = ∏_{i∈S}Q_i ∏_{j∉S}P_j` (`jointProj`) and
`1_{n₊=k} = Σ_{|S|=k} E_S` (`secProj`), and letting `A` be the set of *interaction*
slots of the potential term under consideration, the hypothesis of the statement says
that the pairing

    I(S,T) = ∫_{abox} E_S Φ · W · E_T Φ

vanishes whenever the two sectors have different *free* parts `S ∩ (X∖A)` and
`T ∩ (X∖A)` (this is the slot-mean orthogonality, the content of FS's localisation).
Under that hypothesis the band sum

    Σ_k ∫ 1_{n₊=k} Φ · W · 1_{n₊=k+1} Φ

equals the sum over the triples `(R,U,V)` with `R ⊆ X∖A` (the free part),
`U,V ⊆ A` (the interaction part) and `|V| = |U|+1`.

The proof is the composition of four elementary steps, each of which is proved here:

* `secProj_integral_expansion` — expanding `secProj` turns the box integral of the
  pairing of the two sectors into the double sum of the pairings of the joint sectors
  (the finitely many integrability side conditions come from `hWint` and the continuity
  of the joint sector projections);
* `powersetCard_pairs_reindex` — the `Σ_k Σ_{|S|=k} Σ_{|T|=k+1}`-sum is the sum over
  the pairs `(S,T)` with `|T| = |S|+1` (fibre decomposition of `Finset.powerset` by
  cardinality);
* `sum_pairs_filter_eq_of_free_ne` — by the vanishing hypothesis only the pairs with
  equal free parts contribute;
* `sum_pairs_matching_eq_sum_triples` — such pairs are in bijection with the triples
  `(R,U,V)` via `S = R ∪ U`, `T = R ∪ V` (pure `Finset` combinatorics).

The statement `sum_secProj_eq_sum_triples` is then the `calc` composition of the four.
-/

namespace Work.BoseFixB2.DvApriori.Band

open Submission.BoseGases MeasureTheory

set_option autoImplicit false
set_option linter.unusedVariables false

noncomputable section

/-! ## 1. Cardinality fibres of `Finset.powerset` -/

/-- **`ℝ`-valued form of the `powersetCard` reindexing**: summing over the `k`-element
subsets of `{0,…,n−1}` for all `k ≤ n` is the same as summing over all subsets. -/
lemma sum_powersetCard_eq_sum_powerset_real {n : ℕ} (g : Finset ℕ → ℝ) :
    (∑ k ∈ Finset.range (n + 1), ∑ S ∈ (Finset.range n).powersetCard k, g S)
      = ∑ S ∈ (Finset.range n).powerset, g S := by
  have hmem : ∀ S ∈ (Finset.range n).powerset, S.card ∈ Finset.range (n + 1) := by
    intro S hS
    rw [Finset.mem_range]
    have h1 : S ⊆ Finset.range n := Finset.mem_powerset.mp hS
    have h2 : S.card ≤ n := by simpa using Finset.card_le_card h1
    omega
  have key := Finset.sum_fiberwise_of_maps_to (s := (Finset.range n).powerset)
    (t := Finset.range (n + 1)) (g := Finset.card) hmem g
  simp only [Finset.powersetCard_eq_filter]
  exact key

/-- **The pair reindexing.**  The sum over `k < n`, `S ⊆ {0,…,n−1}` with `|S| = k` and
`T ⊆ {0,…,n−1}` with `|T| = k+1` is the sum over all pairs `(S,T)` of subsets of
`{0,…,n−1}` with `|T| = |S| + 1`. -/
lemma powersetCard_pairs_reindex (I : Finset ℕ → Finset ℕ → ℝ) (n : ℕ) :
    (∑ i ∈ Finset.range n, ∑ S ∈ (Finset.range n).powersetCard i,
        ∑ T ∈ (Finset.range n).powersetCard (i + 1), I S T)
      = ∑ S ∈ (Finset.range n).powerset,
          ∑ T ∈ (Finset.range n).powerset.filter (fun T => T.card = S.card + 1),
            I S T := by
  have hlast : (∑ S ∈ (Finset.range n).powersetCard n,
      ∑ T ∈ (Finset.range n).powersetCard (S.card + 1), I S T) = 0 := by
    refine Finset.sum_eq_zero (fun S hS => ?_)
    have hcard : S.card = n := (Finset.mem_powersetCard.mp hS).2
    rw [hcard, Finset.powersetCard_eq_empty.mpr ?_]
    · simp
    · rw [Finset.card_range]; exact Nat.lt_succ_self n
  calc (∑ i ∈ Finset.range n, ∑ S ∈ (Finset.range n).powersetCard i,
        ∑ T ∈ (Finset.range n).powersetCard (i + 1), I S T)
      = ∑ i ∈ Finset.range n, ∑ S ∈ (Finset.range n).powersetCard i,
          ∑ T ∈ (Finset.range n).powersetCard (S.card + 1), I S T := by
        refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun S hS => ?_))
        rw [(Finset.mem_powersetCard.mp hS).2]
    _ = ∑ i ∈ Finset.range (n + 1), ∑ S ∈ (Finset.range n).powersetCard i,
          ∑ T ∈ (Finset.range n).powersetCard (S.card + 1), I S T := by
        rw [Finset.sum_range_succ, hlast, add_zero]
    _ = ∑ S ∈ (Finset.range n).powerset,
          ∑ T ∈ (Finset.range n).powersetCard (S.card + 1), I S T :=
        sum_powersetCard_eq_sum_powerset_real (n := n) _
    _ = ∑ S ∈ (Finset.range n).powerset,
          ∑ T ∈ (Finset.range n).powerset.filter (fun T => T.card = S.card + 1),
            I S T := by
        simp only [Finset.powersetCard_eq_filter]

/-! ## 2. Expansion of the band integral into a double sum of joint pairings -/

/-- **The integral expansion.**  The box integral of the pairing of the two `n₊`-sectors
`k` and `k+1` is the double sum, over the joint sectors `E_S` (`|S| = k`) and
`E_T` (`|T| = k+1`), of the pairings of the joint sectors.  All the summands are
integrable by the continuity of the joint sector projections and `hWint`. -/
lemma secProj_integral_expansion {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} {W : X n → ℝ}
    (hWint : IntegrableOn W (abox n ℓ)) {Φ : X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (i : ℕ) :
    (∫ x in abox n ℓ, secProj ℓ i Φ x * W x * secProj ℓ (i+1) Φ x)
      = ∑ S ∈ (Finset.range n).powersetCard i,
          ∑ T ∈ (Finset.range n).powersetCard (i+1),
            ∫ x in abox n ℓ, jointProj ℓ S Φ x * W x * jointProj ℓ T Φ x := by
  have hcont : ∀ S : Finset ℕ, Continuous (jointProj ℓ S Φ) :=
    fun S => Work.BoseFixB2.Sector.jointProj_continuous hℓ S hΦ.continuous
  have hint : ∀ S T : Finset ℕ,
      IntegrableOn (fun x => jointProj ℓ S Φ x * W x * jointProj ℓ T Φ x) (abox n ℓ) :=
    fun S T => integrableOn_mul_of_continuous_of_integrable hℓ (hcont S) (hcont T) hWint
  have hpt : ∀ x : X n, secProj ℓ i Φ x * W x * secProj ℓ (i+1) Φ x
      = ∑ S ∈ (Finset.range n).powersetCard i,
          ∑ T ∈ (Finset.range n).powersetCard (i+1),
            jointProj ℓ S Φ x * W x * jointProj ℓ T Φ x := by
    intro x
    simp only [secProj, Finset.sum_apply, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
  have hinner : ∀ S : Finset ℕ,
      (∫ x in abox n ℓ, ∑ T ∈ (Finset.range n).powersetCard (i+1),
          jointProj ℓ S Φ x * W x * jointProj ℓ T Φ x)
        = ∑ T ∈ (Finset.range n).powersetCard (i+1),
            ∫ x in abox n ℓ, jointProj ℓ S Φ x * W x * jointProj ℓ T Φ x :=
    fun S => MeasureTheory.integral_finsetSum _ (fun T _ => hint S T)
  have houter : (∫ x in abox n ℓ, ∑ S ∈ (Finset.range n).powersetCard i,
        ∑ T ∈ (Finset.range n).powersetCard (i+1),
          jointProj ℓ S Φ x * W x * jointProj ℓ T Φ x)
      = ∑ S ∈ (Finset.range n).powersetCard i,
          ∫ x in abox n ℓ, ∑ T ∈ (Finset.range n).powersetCard (i+1),
            jointProj ℓ S Φ x * W x * jointProj ℓ T Φ x :=
    MeasureTheory.integral_finsetSum _
      (fun S _ => MeasureTheory.integrable_finsetSum _ (fun T _ => hint S T))
  calc (∫ x in abox n ℓ, secProj ℓ i Φ x * W x * secProj ℓ (i+1) Φ x)
      = ∫ x in abox n ℓ, ∑ S ∈ (Finset.range n).powersetCard i,
          ∑ T ∈ (Finset.range n).powersetCard (i+1),
            jointProj ℓ S Φ x * W x * jointProj ℓ T Φ x := by
        apply MeasureTheory.integral_congr_ae
        exact Filter.Eventually.of_forall hpt
    _ = ∑ S ∈ (Finset.range n).powersetCard i,
          ∫ x in abox n ℓ, ∑ T ∈ (Finset.range n).powersetCard (i+1),
            jointProj ℓ S Φ x * W x * jointProj ℓ T Φ x := houter
    _ = ∑ S ∈ (Finset.range n).powersetCard i,
          ∑ T ∈ (Finset.range n).powersetCard (i+1),
            ∫ x in abox n ℓ, jointProj ℓ S Φ x * W x * jointProj ℓ T Φ x :=
        Finset.sum_congr rfl (fun S _ => hinner S)

/-! ## 3. The vanishing reduction -/

/-- **The vanishing reduction.**  If the pairing vanishes whenever the free parts
`S ∩ (X∖A)` and `T ∩ (X∖A)` differ, then in the pair sum only the pairs with equal free
parts contribute. -/
lemma sum_pairs_filter_eq_of_free_ne {n : ℕ} {A : Finset ℕ}
    (I : Finset ℕ → Finset ℕ → ℝ)
    (hzero : ∀ S T : Finset ℕ, S ⊆ Finset.range n → T ⊆ Finset.range n →
      S ∩ (Finset.range n \ A) ≠ T ∩ (Finset.range n \ A) → I S T = 0) :
    (∑ S ∈ (Finset.range n).powerset,
        ∑ T ∈ (Finset.range n).powerset.filter (fun T => T.card = S.card + 1), I S T)
      = ∑ S ∈ (Finset.range n).powerset,
          ∑ T ∈ (Finset.range n).powerset.filter
            (fun T => T.card = S.card + 1 ∧
              S ∩ (Finset.range n \ A) = T ∩ (Finset.range n \ A)), I S T := by
  refine Finset.sum_congr rfl (fun S hS => ?_)
  have hSsub : S ⊆ Finset.range n := Finset.mem_powerset.mp hS
  refine (Finset.sum_subset ?_ ?_).symm
  · intro x hx
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2.1⟩
  · intro x hx hxnot
    have hxsub : x ⊆ Finset.range n :=
      Finset.mem_powerset.mp (Finset.mem_filter.mp hx).1
    have hne : S ∩ (Finset.range n \ A) ≠ x ∩ (Finset.range n \ A) := by
      intro hcontra
      exact hxnot (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hx).1,
        ⟨(Finset.mem_filter.mp hx).2, hcontra⟩⟩)
    exact hzero S x hSsub hxsub hne

/-! ## 4. The triple reindexing -/

/-- **The triple reindexing.**  The pairs `(S,T)` of subsets of `{0,…,n−1}` with equal
free parts and `|T| = |S| + 1` are the triples `(R,U,V)` with `R ⊆ X∖A`, `U,V ⊆ A` and
`|V| = |U| + 1`, through `S = R ∪ U`, `T = R ∪ V`. -/
lemma sum_pairs_matching_eq_sum_triples {n : ℕ} {A : Finset ℕ} (hA : A ⊆ Finset.range n)
    (I : Finset ℕ → Finset ℕ → ℝ) :
    (∑ S ∈ (Finset.range n).powerset,
        ∑ T ∈ (Finset.range n).powerset.filter
          (fun T => T.card = S.card + 1 ∧
            S ∩ (Finset.range n \ A) = T ∩ (Finset.range n \ A)), I S T)
      = ∑ R ∈ (Finset.range n \ A).powerset, ∑ U ∈ A.powerset,
          ∑ V ∈ A.powerset.filter (fun V => V.card = U.card + 1),
            I (R ∪ U) (R ∪ V) := by
  have hunion : Finset.range n \ A ∪ A = Finset.range n := Finset.sdiff_union_of_subset hA
  have hdisj : Disjoint (Finset.range n \ A) A :=
    Finset.disjoint_left.mpr (fun a ha hb => (Finset.mem_sdiff.mp ha).2 hb)
  -- a subset of `X` splits into its free part and its interaction part
  have hsplit : ∀ S : Finset ℕ, S ⊆ Finset.range n →
      S = (S ∩ (Finset.range n \ A)) ∪ (S ∩ A) := by
    intro S hS
    calc S = S ∩ Finset.range n := (Finset.inter_eq_left.mpr hS).symm
      _ = S ∩ (Finset.range n \ A ∪ A) := by rw [hunion]
      _ = (S ∩ (Finset.range n \ A)) ∪ (S ∩ A) := Finset.inter_union_distrib_left _ _ _
  have hdisj_int : ∀ S : Finset ℕ,
      Disjoint (S ∩ (Finset.range n \ A)) (S ∩ A) := by
    intro S
    exact Finset.disjoint_left.mpr (fun a ha hb =>
      (Finset.disjoint_left.mp hdisj) (Finset.mem_inter.mp ha).2 (Finset.mem_inter.mp hb).2)
  have hcard : ∀ S : Finset ℕ, S ⊆ Finset.range n →
      S.card = (S ∩ (Finset.range n \ A)).card + (S ∩ A).card := by
    intro S hS
    conv_lhs => rw [hsplit S hS]
    rw [Finset.card_union_of_disjoint (hdisj_int S)]
  -- disjointness of a subset of the free part and a subset of `A`
  have hdisj_fA : ∀ {S T : Finset ℕ}, S ⊆ Finset.range n \ A → T ⊆ A → Disjoint S T := by
    intro S T hS hT
    exact Finset.disjoint_left.mpr (fun x hxS hxT =>
      (Finset.mem_sdiff.mp (hS hxS)).2 (hT hxT))
  have hdisj_Af : ∀ {S : Finset ℕ}, S ⊆ A → Disjoint S (Finset.range n \ A) := by
    intro S hS
    exact Finset.disjoint_left.mpr (fun x hxS hxT =>
      (Finset.mem_sdiff.mp hxT).2 (hS hxS))
  -- the outer sets of the bijection
  have hmain : (∑ x ∈ (Finset.range n).powerset.sigma
        (fun S => (Finset.range n).powerset.filter
          (fun T => T.card = S.card + 1 ∧
            S ∩ (Finset.range n \ A) = T ∩ (Finset.range n \ A))), I x.1 x.2)
      = ∑ y ∈ (Finset.range n \ A).powerset.sigma
          (fun R => A.powerset.sigma
            (fun U => A.powerset.filter (fun V => V.card = U.card + 1))),
          I (y.1 ∪ y.2.1) (y.1 ∪ y.2.2) := by
    refine Finset.sum_nbij'
      (fun a => ⟨a.1 ∩ (Finset.range n \ A), ⟨a.1 ∩ A, a.2 ∩ A⟩⟩)
      (fun b => ⟨b.1 ∪ b.2.1, b.1 ∪ b.2.2⟩) ?_ ?_ ?_ ?_ ?_
    · -- `i` maps the pairs to the triples
      intro a ha
      obtain ⟨ha1, ha2⟩ := Finset.mem_sigma.mp ha
      obtain ⟨ha2', ha2''⟩ := Finset.mem_filter.mp ha2
      have hSsub : a.1 ⊆ Finset.range n := Finset.mem_powerset.mp ha1
      have hTsub : a.2 ⊆ Finset.range n := Finset.mem_powerset.mp ha2'
      rw [Finset.mem_sigma]
      refine ⟨Finset.mem_powerset.mpr Finset.inter_subset_right, ?_⟩
      rw [Finset.mem_sigma]
      refine ⟨Finset.mem_powerset.mpr Finset.inter_subset_right, ?_⟩
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_powerset.mpr Finset.inter_subset_right, ?_⟩
      have hc2 := hcard a.2 hTsub
      rw [ha2''.1, hcard a.1 hSsub, ha2''.2] at hc2
      show (a.2 ∩ A).card = (a.1 ∩ A).card + 1
      omega
    · -- `j` maps the triples to the pairs
      intro a ha
      obtain ⟨ha1, ha2⟩ := Finset.mem_sigma.mp ha
      obtain ⟨ha2_1, ha2_2⟩ := Finset.mem_sigma.mp ha2
      obtain ⟨ha2_2', ha2_2''⟩ := Finset.mem_filter.mp ha2_2
      have ha1sub : a.1 ⊆ Finset.range n \ A := Finset.mem_powerset.mp ha1
      have ha2_1sub : a.2.1 ⊆ A := Finset.mem_powerset.mp ha2_1
      have ha2_2sub : a.2.2 ⊆ A := Finset.mem_powerset.mp ha2_2'
      rw [Finset.mem_sigma]
      refine ⟨Finset.mem_powerset.mpr
        (Finset.union_subset (ha1sub.trans Finset.sdiff_subset) (ha2_1sub.trans hA)), ?_⟩
      rw [Finset.mem_filter]
      refine ⟨Finset.mem_powerset.mpr
        (Finset.union_subset (ha1sub.trans Finset.sdiff_subset) (ha2_2sub.trans hA)), ?_⟩
      refine ⟨?_, ?_⟩
      · show (a.1 ∪ a.2.2).card = (a.1 ∪ a.2.1).card + 1
        have h1 : (a.1 ∪ a.2.2).card = a.1.card + a.2.2.card :=
          Finset.card_union_of_disjoint (hdisj_fA ha1sub ha2_2sub)
        have h2 : (a.1 ∪ a.2.1).card = a.1.card + a.2.1.card :=
          Finset.card_union_of_disjoint (hdisj_fA ha1sub ha2_1sub)
        omega
      · show (a.1 ∪ a.2.1) ∩ (Finset.range n \ A)
            = (a.1 ∪ a.2.2) ∩ (Finset.range n \ A)
        have h2 : (a.1 ∪ a.2.1) ∩ (Finset.range n \ A) = a.1 := by
          rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr ha1sub,
            Finset.disjoint_iff_inter_eq_empty.mp (hdisj_Af ha2_1sub), Finset.union_empty]
        have h3 : (a.1 ∪ a.2.2) ∩ (Finset.range n \ A) = a.1 := by
          rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr ha1sub,
            Finset.disjoint_iff_inter_eq_empty.mp (hdisj_Af ha2_2sub), Finset.union_empty]
        rw [h2, h3]
    · -- `j ∘ i = id` on the pairs
      intro a ha
      obtain ⟨ha1, ha2⟩ := Finset.mem_sigma.mp ha
      obtain ⟨ha2', ha2''⟩ := Finset.mem_filter.mp ha2
      have hSsub : a.1 ⊆ Finset.range n := Finset.mem_powerset.mp ha1
      have hTsub : a.2 ⊆ Finset.range n := Finset.mem_powerset.mp ha2'
      have h1 : (a.1 ∩ (Finset.range n \ A)) ∪ (a.1 ∩ A) = a.1 :=
        (hsplit a.1 hSsub).symm
      have h2 : (a.1 ∩ (Finset.range n \ A)) ∪ (a.2 ∩ A) = a.2 := by
        rw [ha2''.2]
        exact (hsplit a.2 hTsub).symm
      exact Sigma.ext h1 (heq_of_eq h2)
    · -- `i ∘ j = id` on the triples
      intro a ha
      obtain ⟨ha1, ha2⟩ := Finset.mem_sigma.mp ha
      obtain ⟨ha2_1, ha2_2⟩ := Finset.mem_sigma.mp ha2
      obtain ⟨ha2_2', ha2_2''⟩ := Finset.mem_filter.mp ha2_2
      have ha1sub : a.1 ⊆ Finset.range n \ A := Finset.mem_powerset.mp ha1
      have ha2_1sub : a.2.1 ⊆ A := Finset.mem_powerset.mp ha2_1
      have ha2_2sub : a.2.2 ⊆ A := Finset.mem_powerset.mp ha2_2'
      have hf : a.2.1 ∩ (Finset.range n \ A) = ∅ :=
        Finset.disjoint_iff_inter_eq_empty.mp (hdisj_Af ha2_1sub)
      have hAe : a.1 ∩ A = ∅ :=
        Finset.disjoint_iff_inter_eq_empty.mp (hdisj_fA ha1sub (Finset.Subset.refl A))
      have h1 : (a.1 ∪ a.2.1) ∩ (Finset.range n \ A) = a.1 := by
        rw [Finset.union_inter_distrib_right, Finset.inter_eq_left.mpr ha1sub, hf,
          Finset.union_empty]
      have h2 : (a.1 ∪ a.2.1) ∩ A = a.2.1 := by
        rw [Finset.union_inter_distrib_right, hAe, Finset.empty_union,
          Finset.inter_eq_left.mpr ha2_1sub]
      have h3 : (a.1 ∪ a.2.2) ∩ A = a.2.2 := by
        rw [Finset.union_inter_distrib_right, hAe, Finset.empty_union,
          Finset.inter_eq_left.mpr ha2_2sub]
      have hinner : (⟨(a.1 ∪ a.2.1) ∩ A, (a.1 ∪ a.2.2) ∩ A⟩ :
          Sigma fun _ : Finset ℕ => Finset ℕ) = ⟨a.2.1, a.2.2⟩ :=
        Sigma.ext h2 (heq_of_eq h3)
      exact Sigma.ext h1 (heq_of_eq hinner)
    · -- the pairings agree along the bijection
      intro a ha
      obtain ⟨ha1, ha2⟩ := Finset.mem_sigma.mp ha
      obtain ⟨ha2', ha2''⟩ := Finset.mem_filter.mp ha2
      have hSsub : a.1 ⊆ Finset.range n := Finset.mem_powerset.mp ha1
      have hTsub : a.2 ⊆ Finset.range n := Finset.mem_powerset.mp ha2'
      show I a.1 a.2 = I ((a.1 ∩ (Finset.range n \ A)) ∪ (a.1 ∩ A))
        ((a.1 ∩ (Finset.range n \ A)) ∪ (a.2 ∩ A))
      rw [← hsplit a.1 hSsub, ha2''.2, ← hsplit a.2 hTsub]
  -- assemble the two sigma sums
  calc (∑ S ∈ (Finset.range n).powerset,
        ∑ T ∈ (Finset.range n).powerset.filter
          (fun T => T.card = S.card + 1 ∧
            S ∩ (Finset.range n \ A) = T ∩ (Finset.range n \ A)), I S T)
      = ∑ x ∈ (Finset.range n).powerset.sigma
          (fun S => (Finset.range n).powerset.filter
            (fun T => T.card = S.card + 1 ∧
              S ∩ (Finset.range n \ A) = T ∩ (Finset.range n \ A))), I x.1 x.2 := by
        rw [Finset.sum_sigma]
    _ = ∑ y ∈ (Finset.range n \ A).powerset.sigma
          (fun R => A.powerset.sigma
            (fun U => A.powerset.filter (fun V => V.card = U.card + 1))),
          I (y.1 ∪ y.2.1) (y.1 ∪ y.2.2) := hmain
    _ = ∑ R ∈ (Finset.range n \ A).powerset, ∑ U ∈ A.powerset,
          ∑ V ∈ A.powerset.filter (fun V => V.card = U.card + 1),
            I (R ∪ U) (R ∪ V) := by
        rw [Finset.sum_sigma]
        refine Finset.sum_congr rfl (fun R _ => ?_)
        rw [Finset.sum_sigma]

/-! ## 5. The band sum -/

theorem sum_secProj_eq_sum_triples {ℓ : ℝ} (hℓ : 0 < ℓ) {n : ℕ} {A : Finset ℕ}
    (hA : A ⊆ Finset.range n) {W : Submission.BoseGases.X n → ℝ}
    (hWint : MeasureTheory.IntegrableOn W (Submission.BoseGases.abox n ℓ))
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ)
    (hzero : ∀ (S T : Finset ℕ), S ⊆ Finset.range n → T ⊆ Finset.range n →
      S ∩ (Finset.range n \ A) ≠ T ∩ (Finset.range n \ A) →
      (∫ x in Submission.BoseGases.abox n ℓ,
        Work.BoseFixB2.jointProj ℓ S Φ x * W x * Work.BoseFixB2.jointProj ℓ T Φ x) = 0) :
    (∑ i ∈ Finset.range n, ∫ x in Submission.BoseGases.abox n ℓ,
        Work.BoseFixB2.secProj ℓ i Φ x * W x * Work.BoseFixB2.secProj ℓ (i+1) Φ x)
      = ∑ R ∈ (Finset.range n \ A).powerset, ∑ U ∈ A.powerset,
          ∑ V ∈ A.powerset.filter (fun V => V.card = U.card + 1),
            ∫ x in Submission.BoseGases.abox n ℓ,
              Work.BoseFixB2.jointProj ℓ (R ∪ U) Φ x * W x
                * Work.BoseFixB2.jointProj ℓ (R ∪ V) Φ x := by
  have h1 : (∑ i ∈ Finset.range n, ∫ x in Submission.BoseGases.abox n ℓ,
        Work.BoseFixB2.secProj ℓ i Φ x * W x * Work.BoseFixB2.secProj ℓ (i+1) Φ x)
      = ∑ i ∈ Finset.range n, ∑ S ∈ (Finset.range n).powersetCard i,
          ∑ T ∈ (Finset.range n).powersetCard (i+1),
            ∫ x in Submission.BoseGases.abox n ℓ,
              Work.BoseFixB2.jointProj ℓ S Φ x * W x
                * Work.BoseFixB2.jointProj ℓ T Φ x :=
    Finset.sum_congr rfl (fun i _ => secProj_integral_expansion hℓ hWint hΦ i)
  have h2 := powersetCard_pairs_reindex
    (fun S T => ∫ x in Submission.BoseGases.abox n ℓ,
      Work.BoseFixB2.jointProj ℓ S Φ x * W x * Work.BoseFixB2.jointProj ℓ T Φ x) n
  have h3 := sum_pairs_filter_eq_of_free_ne
    (fun S T => ∫ x in Submission.BoseGases.abox n ℓ,
      Work.BoseFixB2.jointProj ℓ S Φ x * W x * Work.BoseFixB2.jointProj ℓ T Φ x) hzero
  have h4 := sum_pairs_matching_eq_sum_triples hA
    (fun S T => ∫ x in Submission.BoseGases.abox n ℓ,
      Work.BoseFixB2.jointProj ℓ S Φ x * W x * Work.BoseFixB2.jointProj ℓ T Φ x)
  exact h1.trans (h2.trans (h3.trans h4))

end

end Work.BoseFixB2.DvApriori.Band
