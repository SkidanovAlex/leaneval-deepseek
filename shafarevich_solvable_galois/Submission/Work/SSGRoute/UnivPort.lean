import Mathlib
import Submission.Work.SSGRoute.pSeries_inter_centralSeries_pow
import Submission.Work.SSGRoute.hallSpan_saturated
import Submission.Work.SSGRoute.UnivPortCore
import Submission.Work.SSGRoute.prop5.lctf.coreDefs
import Submission.Work.SSGRoute.prop5.lctf.mltMonGrp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open scoped commutatorElement

universe u

namespace Work.SSGRoute.UpMw

open Work.SSGRoute.prop5
open Work.SSGRoute.prop5.mw


/-!
# The graded Hall spanning theorem in `ψ`-form

`VspanSize ψ n` is the `ℤ`-span of the values `ψ h` for `h` a **Hall** tree of size `n`.
The lemma `psi_mem_VspanSize` says that `ψ w` lies in that span for `n = Magma.size w`, i.e. the
Hall trees of a fixed size span the degree-`n` part of any Lie-ring-valued bracket evaluation.

This is the degree-graded refinement of `witt.hall_spanning`: the "collecting" algorithm behind
Hall's spanning theorem only ever produces trees with the same `Multiset` of leaves as the pair it
started from, so all Hall trees that occur have the same number of leaves.
-/



-- namespace UpMw (opened above)

variable {X : Type u} [LinearOrder X] {M : Type u} [LieRing M]

/-- Every `Good` tree occurring in the expansion of `⁅ψ x, ψ y⁆` has `size x + size y` leaves,
because its foliage has the same multiset of letters as `foliage x ++ foliage y`. -/
lemma W_le_VspanSize (ψ : Magma X → M) (x y : Magma X) {m : M}
    (hm : m ∈ witt.W ψ x y) : m ∈ VspanSize ψ (Magma.size x + Magma.size y) := by
  rw [witt.W] at hm
  refine Submodule.span_le.mpr ?_ hm
  rintro m ⟨c, hc, rfl⟩
  obtain ⟨hcH, hcms, a, b, hab, hcfol⟩ := hc
  refine Submodule.subset_span ⟨⟨c, hcH, ?_⟩, rfl⟩
  have hcard := congrArg Multiset.card hcms
  simp only [Multiset.card_add, Multiset.coe_card] at hcard
  rw [← Magma.foliage_length c, ← Magma.foliage_length x, ← Magma.foliage_length y]
  exact hcard

/-- The bracket of two **Hall** elements lies in the graded Hall span of the pair's size. -/
lemma bracket_hall_mem_VspanSize (ψ : Magma X → M)
    (hψ : ∀ a b : Magma X, ψ (Magma.mul a b) = ⁅ψ a, ψ b⁆) (x y : Magma X)
    (hx : IsHall x) (hy : IsHall y) :
    ⁅ψ x, ψ y⁆ ∈ VspanSize ψ (Magma.size x + Magma.size y) := by
  rcases eq_or_ne x y with rfl | hne
  · rw [lie_self]; exact Submodule.zero_mem _
  · rcases lt_trichotomy (Magma.foliage x) (Magma.foliage y) with h | h | h
    · exact W_le_VspanSize ψ x y (witt.pair_mem ψ hψ x y hx hy h)
    · exact absurd (witt.hall_foliage_injective_aux hx hy h) hne
    · rw [(lie_skew (ψ x) (ψ y)).symm]
      refine Submodule.neg_mem _ ?_
      have hmem := W_le_VspanSize ψ y x (witt.pair_mem ψ hψ y x hy hx h)
      rwa [Nat.add_comm (Magma.size y) (Magma.size x)] at hmem

/-- The Lie bracket of two elements of graded Hall spans lands in the graded Hall span. -/
lemma bracket_mem_VspanSize (ψ : Magma X → M)
    (hψ : ∀ a b : Magma X, ψ (Magma.mul a b) = ⁅ψ a, ψ b⁆) {p q : M} {n k : ℕ}
    (hp : p ∈ VspanSize ψ n) (hq : q ∈ VspanSize ψ k) :
    ⁅p, q⁆ ∈ VspanSize ψ (n + k) := by
  have key : ∀ p ∈ VspanSize ψ n, ∀ q ∈ VspanSize ψ k, ⁅p, q⁆ ∈ VspanSize ψ (n + k) := by
    intro p hp
    refine Submodule.span_induction
      (p := fun x _ => ∀ q ∈ VspanSize ψ k, ⁅x, q⁆ ∈ VspanSize ψ (n + k)) ?_ ?_ ?_ ?_ hp
    · rintro m ⟨h, rfl⟩ q hq
      refine Submodule.span_induction
        (p := fun y _ => ⁅ψ h.1, y⁆ ∈ VspanSize ψ (n + k)) ?_ ?_ ?_ ?_ hq
      · rintro m' ⟨h', rfl⟩
        have := bracket_hall_mem_VspanSize ψ hψ h.1 h'.1 h.2.1 h'.2.1
        rwa [h.2.2, h'.2.2] at this
      · rw [lie_zero]; exact Submodule.zero_mem _
      · intro a b _ _ ha hb; rw [lie_add]; exact Submodule.add_mem _ ha hb
      · intro r a _ ha; rw [lie_zsmul]; exact Submodule.smul_mem _ r ha
    · intro q _; rw [zero_lie]; exact Submodule.zero_mem _
    · intro a b _ _ ha hb q hq; rw [add_lie]; exact Submodule.add_mem _ (ha q hq) (hb q hq)
    · intro r a _ ha q hq; rw [zsmul_lie]; exact Submodule.smul_mem _ r (ha q hq)
  exact key p hp q hq

theorem psi_mem_VspanSize {X : Type u} [LinearOrder X] {M : Type u} [LieRing M]
    (ψ : Work.SSGRoute.prop5.Magma X → M)
    (hψ : ∀ a b : Work.SSGRoute.prop5.Magma X,
      ψ (Work.SSGRoute.prop5.Magma.mul a b) = ⁅ψ a, ψ b⁆)
    (w : Work.SSGRoute.prop5.Magma X) :
    ψ w ∈ Work.SSGRoute.prop5.mw.VspanSize ψ (Work.SSGRoute.prop5.Magma.size w) := by
  have key : ∀ n : ℕ, ∀ w : Magma X, Magma.size w = n → ψ w ∈ VspanSize ψ (Magma.size w) := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro w hw
      cases w with
      | gen x =>
        exact Submodule.subset_span (Set.mem_range_self
          (f := fun h : {h : Magma X // IsHall h ∧ Magma.size h = Magma.size (Magma.gen x)} =>
            ψ h.1) ⟨Magma.gen x, isHall_gen x, rfl⟩)
      | mul a b =>
        rw [hψ a b, Magma.size_mul]
        refine bracket_mem_VspanSize ψ hψ ?_ ?_
        · exact ih (Magma.size a) (by rw [← hw]; exact Magma.size_left_lt a b) a rfl
        · exact ih (Magma.size b) (by rw [← hw]; exact Magma.size_right_lt a b) b rfl
  exact key (Magma.size w) w rfl

end Work.SSGRoute.UpMw



/-! ## Universe-polymorphic port of the saturation / purity machinery -/

namespace Work.SSGRoute.Up

open Work.SSGRoute.prop5

private def coeffLin (X : Type*) (w : FreeMonoid X) :
    Work.SSGRoute.prop5.FreeAssoc X →ₗ[ℤ] ℤ where
  toFun a := a.coeff w
  map_add' a b := by
    show MonoidAlgebra.coeff (a + b) w = MonoidAlgebra.coeff a w + MonoidAlgebra.coeff b w
    rw [MonoidAlgebra.coeff_add, Finsupp.add_apply]
  map_smul' c a := by
    show MonoidAlgebra.coeff (c • a) w = c • MonoidAlgebra.coeff a w
    rw [MonoidAlgebra.coeff_smul, Finsupp.smul_apply]

private theorem coeffLin_ofList {X : Type*} (w : List X)
    (a : Work.SSGRoute.prop5.FreeAssoc X) :
    coeffLin X (FreeMonoid.ofList w) a = Work.SSGRoute.prop5.coeffF a w := rfl

/-- The "swap" inequality for the two foliage blocks of a Hall product. -/
private theorem foliage_swap {X : Type*} [LinearOrder X] {a b : Work.SSGRoute.prop5.Magma X}
    (hab : Work.SSGRoute.prop5.IsHall (Work.SSGRoute.prop5.Magma.mul a b)) :
    Work.SSGRoute.prop5.Magma.foliage a ++ Work.SSGRoute.prop5.Magma.foliage b
      < Work.SSGRoute.prop5.Magma.foliage b ++ Work.SSGRoute.prop5.Magma.foliage a :=
  Work.SSGRoute.prop5.swap_hall_of_crux
    (fun _ _ h => Work.SSGRoute.prop5.witt.hall_foliage_lt_right h) hab

private theorem monBrk_coeffF_lead {X : Type*} [LinearOrder X]
    {h : Work.SSGRoute.prop5.Magma X} (hh : Work.SSGRoute.prop5.IsHall h) :
    Work.SSGRoute.prop5.coeffF (Work.SSGRoute.prop5.monBrk X h)
        (Work.SSGRoute.prop5.Magma.foliage h) = 1 ∧
      ∀ w : List X, w < Work.SSGRoute.prop5.Magma.foliage h →
        Work.SSGRoute.prop5.coeffF (Work.SSGRoute.prop5.monBrk X h) w = 0 := by
  have hswap : ∀ a b : Work.SSGRoute.prop5.Magma X,
      Work.SSGRoute.prop5.IsHall (Work.SSGRoute.prop5.Magma.mul a b) →
      Work.SSGRoute.prop5.Magma.foliage a ++ Work.SSGRoute.prop5.Magma.foliage b
        < Work.SSGRoute.prop5.Magma.foliage b ++ Work.SSGRoute.prop5.Magma.foliage a :=
    fun _ _ hab => foliage_swap hab
  exact ⟨(Work.SSGRoute.prop5.witt.leading_term_coeff hh hswap).1,
    fun w hw => (Work.SSGRoute.prop5.witt.leading_term_coeff hh hswap).2 w hw⟩

/-- A `ℤ`-algebra element divisible by `n ≠ 0` vanishes. -/
private theorem eq_zero_of_smul_eq_zero {X : Type*} {n : ℤ} (hn : n ≠ 0)
    {u : Work.SSGRoute.prop5.FreeAssoc X} (h : n • u = 0) : u = 0 := by
  apply MonoidAlgebra.ext
  ext w
  have h1 : n * u.coeff w = 0 := by
    have h2 : (n • u).coeff w = 0 := by
      rw [h, MonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    rwa [MonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul] at h2
  rcases mul_eq_zero.mp h1 with h3 | h3
  · exact absurd h3 hn
  · rw [h3, MonoidAlgebra.coeff_zero, Finsupp.zero_apply]

/-- **Purity of the span of a unitriangular family.**  Let `b : ι → ℤ⟨X⟩` be a family of elements
whose "leading words" `f i` are pairwise distinct, `b i` having coefficient `1` at `f i` and
coefficient `0` at every lexicographically smaller word.  Then the `ℤ`-span of the family is
saturated: for `n ≠ 0`, `n • v` in the span implies `v` in the span.

Proof: write `n • v = Σ_{i ∈ s} α i • b i`.  If `s ≠ ∅`, pick `i₀ ∈ s` with `f i₀` minimal.  For
`i ∈ s`, `i ≠ i₀` we have `f i₀ < f i`, so `b i` contributes `0` to the coefficient of `f i₀`;
hence the coefficient of `n • v` at `f i₀` is `α i₀`, i.e. `n ∣ α i₀`.  Removing the term
`i₀` and dividing by `n`, the number of terms drops, and induction on `s.card` concludes. -/
theorem hallSpan_pure_of_leading {X : Type*} [LinearOrder X] {ι : Type*}
    (f : ι → List X) (hf : Function.Injective f) (b : ι → Work.SSGRoute.prop5.FreeAssoc X)
    (hlead : ∀ i, Work.SSGRoute.prop5.coeffF (b i) (f i) = 1)
    (hbelow : ∀ i w, w < f i → Work.SSGRoute.prop5.coeffF (b i) w = 0)
    (n : ℤ) (hn : n ≠ 0) (v : Work.SSGRoute.prop5.FreeAssoc X)
    (h : n • v ∈ Submodule.span ℤ (Set.range b)) :
    v ∈ Submodule.span ℤ (Set.range b) := by
  classical
  obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp (R := ℤ) (v := b)).mp h
  have key : ∀ (m : ℕ) (u : Work.SSGRoute.prop5.FreeAssoc X) (s : Finset ι) (α : ι → ℤ),
      s.card = m → (∑ i ∈ s, α i • b i) = n • u →
      u ∈ Submodule.span ℤ (Set.range b) := by
    intro m
    induction m using Nat.strong_induction_on with
    | _ m ih =>
      intro u s α hcard hsum
      rcases s.eq_empty_or_nonempty with hem | hne
      · rw [hem, Finset.sum_empty] at hsum
        rw [eq_zero_of_smul_eq_zero hn hsum.symm]
        exact Submodule.zero_mem _
      · obtain ⟨i₀, hi₀, hmin⟩ := Finset.exists_min_image s f hne
        have hsingle : coeffLin X (FreeMonoid.ofList (f i₀)) (α i₀ • b i₀) = α i₀ := by
          rw [map_smul, smul_eq_mul, coeffLin_ofList, hlead i₀, mul_one]
        have hsum_coeff : coeffLin X (FreeMonoid.ofList (f i₀)) (∑ i ∈ s, α i • b i)
            = α i₀ := by
          rw [map_sum, ← hsingle]
          refine Finset.sum_eq_single i₀ ?_ ?_
          · intro i hi hne'
            have hlt : f i₀ < f i := lt_of_le_of_ne (hmin i hi) (fun hh => hne' (hf hh.symm))
            rw [map_smul, smul_eq_mul, coeffLin_ofList, hbelow i (f i₀) hlt, mul_zero]
          · intro h
            exact absurd hi₀ h
        have hcoeff : coeffLin X (FreeMonoid.ofList (f i₀)) (∑ i ∈ s, α i • b i)
            = coeffLin X (FreeMonoid.ofList (f i₀)) (n • u) := by rw [hsum]
        have hα : α i₀ = n * Work.SSGRoute.prop5.coeffF u (f i₀) := by
          rw [← hsum_coeff, hcoeff, map_smul, coeffLin_ofList, smul_eq_mul]
        have hstep : (∑ i ∈ s.erase i₀, α i • b i)
            = n • (u - (Work.SSGRoute.prop5.coeffF u (f i₀)) • b i₀) := by
          have hsplit : (∑ i ∈ s, α i • b i)
              = (∑ i ∈ s.erase i₀, α i • b i) + α i₀ • b i₀ :=
            (Finset.sum_erase_add s (fun i => α i • b i) hi₀).symm
          rw [hsplit] at hsum
          have hfac : n • (u - (Work.SSGRoute.prop5.coeffF u (f i₀)) • b i₀)
              = n • u - α i₀ • b i₀ := by
            rw [smul_sub, ← mul_smul, ← hα]
          rw [hfac]
          exact eq_sub_of_add_eq hsum
        have hpos : 0 < m := by
          rw [← hcard]
          exact Finset.card_pos.mpr hne
        have hcard' : (s.erase i₀).card < m := by
          rw [Finset.card_erase_of_mem hi₀, hcard]
          exact Nat.sub_lt hpos Nat.one_pos
        have hrec := ih (s.erase i₀).card hcard'
          (u - (Work.SSGRoute.prop5.coeffF u (f i₀)) • b i₀) (s.erase i₀) α rfl hstep
        have husplit : u = (u - (Work.SSGRoute.prop5.coeffF u (f i₀)) • b i₀)
            + (Work.SSGRoute.prop5.coeffF u (f i₀)) • b i₀ := by abel
        rw [husplit]
        exact Submodule.add_mem _ hrec
          (Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i₀)))
  have hsum : (∑ i ∈ c.support, c i • b i) = n • v := by
    rw [← Finsupp.sum_of_support_subset c (Finset.Subset.refl _) (fun i r => r • b i) (by simp)]
    exact hc
  exact key c.support.card v c.support (fun i => c i) rfl hsum

/-! ## The coordinatewise quotient by `n` -/

/-- The element of `ℤ⟨X⟩` obtained by dividing every coefficient of `a` by `n`. -/
private noncomputable def divCoeff (X : Type*) (n : ℤ) (a : Work.SSGRoute.prop5.FreeAssoc X) :
    Work.SSGRoute.prop5.FreeAssoc X :=
  MonoidAlgebra.ofCoeff (a.coeff.mapRange (fun c => c / n) (by simp))

private theorem divCoeff_coeff (X : Type*) (n : ℤ) (a : Work.SSGRoute.prop5.FreeAssoc X)
    (w : FreeMonoid X) : (divCoeff X n a).coeff w = a.coeff w / n := by
  rw [divCoeff, MonoidAlgebra.coeff_ofCoeff, Finsupp.mapRange_apply]

/-! ## Saturation of the degree-`j` Hall span -/

theorem hallSpan_saturated_u {X : Type u} [LinearOrder X] (j : ℕ) (n : ℤ) (hn : n ≠ 0)
    (a : Work.SSGRoute.prop5.FreeAssoc X)
    (ha : a ∈ Submodule.span ℤ {b : Work.SSGRoute.prop5.FreeAssoc X |
      ∃ h : Work.SSGRoute.prop5.Magma X, Work.SSGRoute.prop5.IsHall h ∧
        Work.SSGRoute.prop5.Magma.size h = j ∧ b = Work.SSGRoute.prop5.monBrk X h})
    (hdiv : ∀ w : FreeMonoid X, n ∣ a.coeff w) :
    ∃ b ∈ Submodule.span ℤ {b : Work.SSGRoute.prop5.FreeAssoc X |
      ∃ h : Work.SSGRoute.prop5.Magma X, Work.SSGRoute.prop5.IsHall h ∧
        Work.SSGRoute.prop5.Magma.size h = j ∧ b = Work.SSGRoute.prop5.monBrk X h},
      a = n • b := by
  classical
  -- the set of generators, written as the range of the (foliage-injective) Hall family
  have hrange : {b : Work.SSGRoute.prop5.FreeAssoc X |
        ∃ h : Work.SSGRoute.prop5.Magma X, Work.SSGRoute.prop5.IsHall h ∧
          Work.SSGRoute.prop5.Magma.size h = j ∧ b = Work.SSGRoute.prop5.monBrk X h}
      = Set.range (fun h : {h : Work.SSGRoute.prop5.Magma X //
          Work.SSGRoute.prop5.IsHall h ∧ Work.SSGRoute.prop5.Magma.size h = j} =>
            Work.SSGRoute.prop5.monBrk X h.1) := by
    ext b
    constructor
    · rintro ⟨h, hh, hs, rfl⟩
      exact ⟨⟨h, hh, hs⟩, rfl⟩
    · rintro ⟨h, rfl⟩
      exact ⟨h.1, h.2.1, h.2.2, rfl⟩
  have hle₁ : Submodule.span ℤ {b : Work.SSGRoute.prop5.FreeAssoc X |
        ∃ h : Work.SSGRoute.prop5.Magma X, Work.SSGRoute.prop5.IsHall h ∧
          Work.SSGRoute.prop5.Magma.size h = j ∧ b = Work.SSGRoute.prop5.monBrk X h}
      ≤ Submodule.span ℤ (Set.range (fun h : {h : Work.SSGRoute.prop5.Magma X //
          Work.SSGRoute.prop5.IsHall h ∧ Work.SSGRoute.prop5.Magma.size h = j} =>
            Work.SSGRoute.prop5.monBrk X h.1)) :=
    Submodule.span_mono (by rw [hrange])
  have hle₂ : Submodule.span ℤ (Set.range (fun h : {h : Work.SSGRoute.prop5.Magma X //
        Work.SSGRoute.prop5.IsHall h ∧ Work.SSGRoute.prop5.Magma.size h = j} =>
          Work.SSGRoute.prop5.monBrk X h.1))
      ≤ Submodule.span ℤ {b : Work.SSGRoute.prop5.FreeAssoc X |
        ∃ h : Work.SSGRoute.prop5.Magma X, Work.SSGRoute.prop5.IsHall h ∧
          Work.SSGRoute.prop5.Magma.size h = j ∧ b = Work.SSGRoute.prop5.monBrk X h} :=
    Submodule.span_mono (by rw [← hrange])
  have haR : a ∈ Submodule.span ℤ (Set.range (fun h : {h : Work.SSGRoute.prop5.Magma X //
      Work.SSGRoute.prop5.IsHall h ∧ Work.SSGRoute.prop5.Magma.size h = j} =>
        Work.SSGRoute.prop5.monBrk X h.1)) := hle₁ ha
  -- divide the coefficients of `a` by `n`
  have hmul : ∀ w : FreeMonoid X, n * (divCoeff X n a).coeff w = a.coeff w := by
    intro w
    rw [divCoeff_coeff]
    exact Int.mul_ediv_cancel' (hdiv w)
  have ham : a = n • divCoeff X n a := by
    apply MonoidAlgebra.ext
    rw [MonoidAlgebra.coeff_smul]
    ext w
    rw [Finsupp.smul_apply, smul_eq_mul]
    exact (hmul w).symm
  -- purity of the Hall span, applied to the unitriangular family of bracket monomials
  have hmR : divCoeff X n a ∈ Submodule.span ℤ (Set.range (fun h :
      {h : Work.SSGRoute.prop5.Magma X //
        Work.SSGRoute.prop5.IsHall h ∧ Work.SSGRoute.prop5.Magma.size h = j} =>
          Work.SSGRoute.prop5.monBrk X h.1)) :=
    hallSpan_pure_of_leading
      (fun h : {h : Work.SSGRoute.prop5.Magma X //
          Work.SSGRoute.prop5.IsHall h ∧ Work.SSGRoute.prop5.Magma.size h = j} =>
            Work.SSGRoute.prop5.Magma.foliage h.1)
      (fun h₁ h₂ hfol => Subtype.ext
        (Work.SSGRoute.prop5.witt.hall_foliage_injective_aux h₁.2.1 h₂.2.1 hfol))
      (fun h => Work.SSGRoute.prop5.monBrk X h.1)
      (fun h => (monBrk_coeffF_lead h.2.1).1)
      (fun h w hw => (monBrk_coeffF_lead h.2.1).2 w hw)
      n hn (divCoeff X n a) (by rw [← ham]; exact haR)
  exact ⟨divCoeff X n a, hle₂ hmR, ham⟩


end Work.SSGRoute.Up

/-! ## Universe-polymorphic port of `lctf.mlt_monGrp_sub_mem` -/

namespace Work.SSGRoute.UpLctf

open Work.SSGRoute.prop5
open Work.SSGRoute.UpLctf

theorem monBrk_mem_fil (X : Type*) (c : Magma X) :
    monBrk X c ∈ fil X (Magma.size c) := by
  induction c with
  | gen x =>
      rw [monBrk_gen, Magma.size_gen]
      exact Ideal.subset_span ⟨FreeMonoid.of x, by simp, rfl⟩
  | mul a b iha ihb =>
      rw [monBrk_mul, Magma.size_mul]
      refine Submodule.sub_mem _ ?_ ?_
      · exact fil_mul_le X (Magma.size a) (Magma.size b) (Ideal.mul_mem_mul iha ihb)
      · exact fil_antitone X (by omega)
          (fil_mul_le X (Magma.size b) (Magma.size a) (Ideal.mul_mem_mul ihb iha))

/-- The leading term of the group commutator monomial of a tree `c` agrees with the bracketed
monomial `monBrk X c` modulo `filq X N (size c + 1)`. -/
theorem mlt_monGrp_sub_mem_aux (X : Type u) :
    ∀ (c : Magma X) (N : ℕ), Magma.size c + 1 ≤ N →
      mlt N (monGrp X c) - Ideal.Quotient.mk (fil X N) (monBrk X c) ∈
        filq X N (Magma.size c + 1) := by
  intro c
  induction c with
  | gen x =>
      intro N hN
      rw [monGrp_gen, Magma.size_gen, monBrk_gen, mlt_of]
      rw [sub_self]
      exact Submodule.zero_mem _
  | mul a b iha ihb =>
      intro N hN
      have hpaq : Magma.size a + Magma.size b + 1 ≤ N := by simpa [Magma.size_mul] using hN
      have hp : 1 ≤ Magma.size a := Magma.size_pos a
      have hq : 1 ≤ Magma.size b := Magma.size_pos b
      have hpa : Magma.size a + 1 ≤ N := by omega
      have hqb : Magma.size b + 1 ≤ N := by omega
      have ha := iha N hpa
      have hb := ihb N hqb
      have hLTa : mlt N (monGrp X a) ∈ filq X N (Magma.size a) :=
        mlt_mem_filq N (Magma.size a) hp (by omega) (monGrp_mem_Gam a)
      have hLTb : mlt N (monGrp X b) ∈ filq X N (Magma.size b) :=
        mlt_mem_filq N (Magma.size b) hq (by omega) (monGrp_mem_Gam b)
      have hBa : Ideal.Quotient.mk (fil X N) (monBrk X a) ∈ filq X N (Magma.size a) :=
        Ideal.mem_map_of_mem _ (monBrk_mem_fil X a)
      have hBb : Ideal.Quotient.mk (fil X N) (monBrk X b) ∈ filq X N (Magma.size b) :=
        Ideal.mem_map_of_mem _ (monBrk_mem_fil X b)
      have hcomm := mlt_commutator N (Magma.size a) (Magma.size b) hp hq hpaq
        (u := monGrp X a) (v := monGrp X b)
        (monGrp_mem_Gam a) (monGrp_mem_Gam b)
      have hcongr : (mlt N (monGrp X a) * mlt N (monGrp X b)
            - mlt N (monGrp X b) * mlt N (monGrp X a))
          - (Ideal.Quotient.mk (fil X N) (monBrk X a) * Ideal.Quotient.mk (fil X N) (monBrk X b)
            - Ideal.Quotient.mk (fil X N) (monBrk X b) * Ideal.Quotient.mk (fil X N) (monBrk X a))
          ∈ filq X N (Magma.size a + Magma.size b + 1) := by
        have h1 : mlt N (monGrp X a) * mlt N (monGrp X b)
            - Ideal.Quotient.mk (fil X N) (monBrk X a) * Ideal.Quotient.mk (fil X N) (monBrk X b)
            ∈ filq X N (Magma.size a + Magma.size b + 1) := by
          have hA := filq_antitone X N
            (by omega : Magma.size a + Magma.size b + 1 ≤ (Magma.size a + 1) + Magma.size b)
            (mul_mem_filq X N (Magma.size a + 1) (Magma.size b) ha hLTb)
          have hB := filq_antitone X N
            (by omega : Magma.size a + Magma.size b + 1 ≤ Magma.size a + (Magma.size b + 1))
            (mul_mem_filq X N (Magma.size a) (Magma.size b + 1) hBa hb)
          have heq : mlt N (monGrp X a) * mlt N (monGrp X b)
              - Ideal.Quotient.mk (fil X N) (monBrk X a) * Ideal.Quotient.mk (fil X N) (monBrk X b)
              = (mlt N (monGrp X a) - Ideal.Quotient.mk (fil X N) (monBrk X a))
                  * mlt N (monGrp X b)
                + Ideal.Quotient.mk (fil X N) (monBrk X a)
                  * (mlt N (monGrp X b) - Ideal.Quotient.mk (fil X N) (monBrk X b)) := by
            noncomm_ring
          rw [heq]
          exact Submodule.add_mem _ hA hB
        have h2 : mlt N (monGrp X b) * mlt N (monGrp X a)
            - Ideal.Quotient.mk (fil X N) (monBrk X b) * Ideal.Quotient.mk (fil X N) (monBrk X a)
            ∈ filq X N (Magma.size a + Magma.size b + 1) := by
          have hA := filq_antitone X N
            (by omega : Magma.size a + Magma.size b + 1 ≤ (Magma.size b + 1) + Magma.size a)
            (mul_mem_filq X N (Magma.size b + 1) (Magma.size a) hb hLTa)
          have hB := filq_antitone X N
            (by omega : Magma.size a + Magma.size b + 1 ≤ Magma.size b + (Magma.size a + 1))
            (mul_mem_filq X N (Magma.size b) (Magma.size a + 1) hBb ha)
          have heq : mlt N (monGrp X b) * mlt N (monGrp X a)
              - Ideal.Quotient.mk (fil X N) (monBrk X b) * Ideal.Quotient.mk (fil X N) (monBrk X a)
              = (mlt N (monGrp X b) - Ideal.Quotient.mk (fil X N) (monBrk X b))
                  * mlt N (monGrp X a)
                + Ideal.Quotient.mk (fil X N) (monBrk X b)
                  * (mlt N (monGrp X a) - Ideal.Quotient.mk (fil X N) (monBrk X a)) := by
            noncomm_ring
          rw [heq]
          exact Submodule.add_mem _ hA hB
        have heq2 : (mlt N (monGrp X a) * mlt N (monGrp X b)
              - mlt N (monGrp X b) * mlt N (monGrp X a))
            - (Ideal.Quotient.mk (fil X N) (monBrk X a) * Ideal.Quotient.mk (fil X N) (monBrk X b)
              - Ideal.Quotient.mk (fil X N) (monBrk X b) * Ideal.Quotient.mk (fil X N) (monBrk X a))
            = (mlt N (monGrp X a) * mlt N (monGrp X b)
                - Ideal.Quotient.mk (fil X N) (monBrk X a) * Ideal.Quotient.mk (fil X N) (monBrk X b))
              - (mlt N (monGrp X b) * mlt N (monGrp X a)
                - Ideal.Quotient.mk (fil X N) (monBrk X b) * Ideal.Quotient.mk (fil X N) (monBrk X a)) := by
            noncomm_ring
        rw [heq2]
        exact Submodule.sub_mem _ h1 h2
      have hsum : mlt N ⁅monGrp X a, monGrp X b⁆
            - (Ideal.Quotient.mk (fil X N) (monBrk X a) * Ideal.Quotient.mk (fil X N) (monBrk X b)
              - Ideal.Quotient.mk (fil X N) (monBrk X b) * Ideal.Quotient.mk (fil X N) (monBrk X a))
            ∈ filq X N (Magma.size a + Magma.size b + 1) := by
        have heq : mlt N ⁅monGrp X a, monGrp X b⁆
              - (Ideal.Quotient.mk (fil X N) (monBrk X a) * Ideal.Quotient.mk (fil X N) (monBrk X b)
                - Ideal.Quotient.mk (fil X N) (monBrk X b) * Ideal.Quotient.mk (fil X N) (monBrk X a))
              = (mlt N ⁅monGrp X a, monGrp X b⁆
                  - (mlt N (monGrp X a) * mlt N (monGrp X b)
                    - mlt N (monGrp X b) * mlt N (monGrp X a)))
                + ((mlt N (monGrp X a) * mlt N (monGrp X b)
                    - mlt N (monGrp X b) * mlt N (monGrp X a))
                  - (Ideal.Quotient.mk (fil X N) (monBrk X a) * Ideal.Quotient.mk (fil X N) (monBrk X b)
                    - Ideal.Quotient.mk (fil X N) (monBrk X b)
                      * Ideal.Quotient.mk (fil X N) (monBrk X a))) := by
            noncomm_ring
        rw [heq]
        exact Submodule.add_mem _ hcomm hcongr
      rw [monGrp_mul, monBrk_mul, Magma.size_mul, map_sub, map_mul, map_mul]
      exact hsum

theorem mlt_monGrp_sub_mem (X : Type u) (N : ℕ) (c : Work.SSGRoute.prop5.Magma X)
    (hN : Work.SSGRoute.prop5.Magma.size c + 1 ≤ N) :
    Work.SSGRoute.UpLctf.mlt N (Work.SSGRoute.UpLctf.monGrp X c) -
      Ideal.Quotient.mk (Work.SSGRoute.prop5.fil X N)
        (Work.SSGRoute.prop5.monBrk X c) ∈
      Work.SSGRoute.prop5.filq X N (Work.SSGRoute.prop5.Magma.size c + 1) :=
  mlt_monGrp_sub_mem_aux X c N hN


end Work.SSGRoute.UpLctf

/-! ## Universe-polymorphic port of the SSPow purity chain -/

namespace Work.SSGRoute.Up

open Work.SSGRoute.prop5

attribute [local instance 100] LieRing.ofAssociativeRing



open Work.SSGRoute.prop5

attribute [local instance 100] LieRing.ofAssociativeRing

variable {X : Type u}

/-- The paper's `γ_k` (Mathlib indexing: `lowerCentralSeries (k-1)`). -/
abbrev gam (X : Type u) (k : ℕ) : Subgroup (FreeGroup X) :=
  (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries k

/-- The `ℤ`-span of the commutator monomials `monBrk X h` for `h` a Hall tree of size `j`. -/
def hallSpan (X : Type u) [LinearOrder X] (j : ℕ) : Submodule ℤ (FreeAssoc X) :=
  Submodule.span ℤ {b : FreeAssoc X |
    ∃ h : Magma X, IsHall h ∧ Magma.size h = j ∧ b = monBrk X h}

/-! ## Homogeneity of the bracketed monomial -/

/-- Every word occurring in `monBrk X c` has length `Magma.size c`. -/
theorem monBrk_coeff_length (c : Magma X) {w : FreeMonoid X}
    (h : (monBrk X c).coeff w ≠ 0) : w.length = Magma.size c := by
  classical
  have hmain : ∀ (c : Magma X) (v : FreeMonoid X), v ∈ (monBrk X c).coeff.support →
      v.length = Magma.size c := by
    intro c
    induction c with
    | gen x =>
        intro v hv
        rw [monBrk_gen] at hv
        rw [Finsupp.mem_support_iff] at hv
        rw [MonoidAlgebra.coeff_single] at hv
        have hv' : v = FreeMonoid.of x := by
          by_contra hne
          exact hv (Finsupp.single_eq_of_ne hne)
        rw [hv']
        simp
    | mul a b iha ihb =>
        intro v hv
        rw [monBrk_mul, MonoidAlgebra.coeff_sub] at hv
        rcases Finset.mem_union.mp (Finsupp.support_sub hv) with hv | hv
        · rcases Finset.mem_mul.mp
            (MonoidAlgebra.support_coeff_mul_subset (monBrk X a) (monBrk X b) hv) with
            ⟨u, hu, u', hu', rfl⟩
          rw [FreeMonoid.length_mul, iha u hu, ihb u' hu', Magma.size_mul]
        · rcases Finset.mem_mul.mp
            (MonoidAlgebra.support_coeff_mul_subset (monBrk X b) (monBrk X a) hv) with
            ⟨u, hu, u', hu', rfl⟩
          rw [FreeMonoid.length_mul, ihb u hu, iha u' hu', Magma.size_mul, Nat.add_comm]
  exact hmain c w (Finsupp.mem_support_iff.mpr h)

/-- Elements of `hallSpan X j` have no coefficients outside words of length `j`. -/
theorem hallSpan_coeff_eq_zero {X : Type u} [LinearOrder X] {j : ℕ} {a : FreeAssoc X}
    (ha : a ∈ hallSpan X j)
    {w : FreeMonoid X} (hw : w.length ≠ j) : a.coeff w = 0 := by
  classical
  have key : ∀ a ∈ hallSpan X j, ∀ w : FreeMonoid X, w.length ≠ j → a.coeff w = 0 := by
    intro a ha
    refine Submodule.span_induction (p := fun a _ => ∀ w : FreeMonoid X, w.length ≠ j →
      a.coeff w = 0) ?_ ?_ ?_ ?_ ha
    · rintro b ⟨h, hH, hsz, rfl⟩ w hw
      by_contra hne
      exact hw (by rw [monBrk_coeff_length h hne, hsz])
    · intro w hw; rw [MonoidAlgebra.coeff_zero, Finsupp.zero_apply]
    · intro x y _ _ hx hy w hw
      rw [MonoidAlgebra.coeff_add, Finsupp.add_apply, hx w hw, hy w hw, add_zero]
    · intro c x _ hx w hw
      rw [MonoidAlgebra.coeff_smul, Finsupp.smul_apply, hx w hw, smul_zero]
  exact key a ha w hw

/-! ## Extraction of a finite presentation in the Hall span -/

/-- An element of the Hall span is a finite `ℤ`-linear combination of the `monBrk` of Hall trees
of size `j`. -/
theorem exists_finsupp_of_mem_hallSpan {X : Type u} [LinearOrder X] {j : ℕ} {a : FreeAssoc X}
    (ha : a ∈ hallSpan X j) :
    ∃ d : {h : Magma X // IsHall h ∧ Magma.size h = j} →₀ ℤ,
      a = ∑ h ∈ d.support, d h • monBrk X h.1 := by
  rw [hallSpan] at ha
  have ha' : a ∈ Submodule.span ℤ
      (Set.range (fun h : {h : Magma X // IsHall h ∧ Magma.size h = j} => monBrk X h.1)) := by
    refine Submodule.span_mono ?_ ha
    rintro b ⟨h, hH, hsz, rfl⟩
    exact ⟨⟨h, hH, hsz⟩, rfl⟩
  rw [← Finsupp.range_linearCombination (ℤ)
    (v := fun h : {h : Magma X // IsHall h ∧ Magma.size h = j} => monBrk X h.1)] at ha'
  obtain ⟨d, hd⟩ := ha'
  refine ⟨d, ?_⟩
  rw [← hd, Finsupp.linearCombination_apply,
    Finsupp.sum_of_support_subset d (Finset.Subset.refl _) (fun h r => r • monBrk X h.1)
      (by simp)]
/-- Coefficients are additive over finite sums. -/
theorem sum_coeff {ι : Type} (s : Finset ι) (f : ι → MonoidAlgebra ℤ (FreeMonoid X))
    (W : FreeMonoid X) : (∑ i ∈ s, f i).coeff W = ∑ i ∈ s, (f i).coeff W := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s has ih
    rw [Finset.sum_insert has, Finset.sum_insert has, MonoidAlgebra.coeff_add, Finsupp.add_apply,
      ih]

/-! ## Saturation of the Hall span -/

/-- The leading term of the bracketed monomial of a Hall tree: the foliage occurs with coefficient
`1` and every smaller word with coefficient `0`. -/
theorem hall_lead {X : Type u} [LinearOrder X] {h : Magma X} (hH : IsHall h) :
    (monBrk X h).coeff (FreeMonoid.ofList (Magma.foliage h)) = 1 ∧
      ∀ (w : List X), w < Magma.foliage h → (monBrk X h).coeff (FreeMonoid.ofList w) = 0 :=
  mw.hlead_monBrk h hH

/-- The bracket monomial of an arbitrary tree of size `j` lies in the Hall span of degree `j`. -/
theorem monBrk_mem_hallSpan {X : Type u} [LinearOrder X] (c : Magma X) :
    monBrk X c ∈ hallSpan X (Magma.size c) := by
  have h := Work.SSGRoute.UpMw.psi_mem_VspanSize (fun c : Magma X => monBrk X c)
    (fun a b => monBrk_mul a b) c
  rw [mw.VspanSize] at h
  refine Submodule.span_mono ?_ h
  rintro b ⟨h, rfl⟩
  exact ⟨h.1, h.2.1, h.2.2, rfl⟩

/-- The Hall span of degree `j` is contained in the `j`-th length filtration piece. -/
theorem hallSpan_le_fil {X : Type u} [LinearOrder X] (j : ℕ) :
    (hallSpan X j : Set (FreeAssoc X)) ⊆ (fil X j : Set (FreeAssoc X)) := by
  intro b hb
  simp only [hallSpan] at hb
  refine Submodule.span_induction (p := fun b _ => b ∈ (fil X j : Set (FreeAssoc X)))
    ?_ ?_ ?_ ?_ hb
  · rintro b ⟨h, hH, hsz, rfl⟩
    have hfil := Work.SSGRoute.UpLctf.monBrk_mem_fil X h
    rwa [hsz] at hfil
  · exact (fil X j).zero_mem
  · intro x y _ _ hx hy
    exact (fil X j).add_mem hx hy
  · intro r x _ hx
    rw [Algebra.smul_def]
    exact Ideal.mul_mem_left (fil X j) ((r : ℤ) : FreeAssoc X) hx

theorem hallSpan_sat {X : Type u} [LinearOrder X] (j : ℕ) (n : ℤ) (hn : n ≠ 0)
    (a : FreeAssoc X) (ha : a ∈ hallSpan X j) (hdiv : ∀ w : FreeMonoid X, n ∣ a.coeff w) :
    ∃ b ∈ hallSpan X j, a = n • b :=
  hallSpan_saturated_u (X := X) j n hn a ha hdiv

/-! ## The image of the Hall span under the Magnus leading term -/

/-- Every element of the Hall span of degree `j` is the Magnus leading term of an element of
`γ_{j-1}`. -/
theorem exists_gamma_of_hallSpan {X : Type u} [LinearOrder X] (j : ℕ) (hj : 1 ≤ j)
    {b : FreeAssoc X} (hb : b ∈ hallSpan X j) :
    ∃ w ∈ gam X (j-1), magLT X j w = Ideal.Quotient.mk (fil X (j+1)) b := by
  classical
  have hb' : b ∈ Submodule.span ℤ {b : FreeAssoc X |
      ∃ h : Magma X, IsHall h ∧ Magma.size h = j ∧ b = monBrk X h} := by
    simpa [hallSpan] using hb
  revert hb'
  refine Submodule.span_induction (p := fun b _ => ∃ w ∈ gam X (j-1),
    magLT X j w = Ideal.Quotient.mk (fil X (j+1)) b) ?_ ?_ ?_ ?_
  · rintro b ⟨h, hH, hsz, rfl⟩
    refine ⟨Work.SSGRoute.UpLctf.monGrp X h, ?_, ?_⟩
    · have hmem' : Work.SSGRoute.UpLctf.monGrp X h ∈ Work.SSGRoute.UpLctf.Gam X (j-1) := by
        simpa [hsz] using Work.SSGRoute.UpLctf.monGrp_mem_Gam (X := X) h
      show Work.SSGRoute.UpLctf.monGrp X h ∈ (⊤ : Subgroup (FreeGroup X)).lowerCentralSeries (j - 1)
      exact hmem'
    · have hsub := Work.SSGRoute.UpLctf.mlt_monGrp_sub_mem X (j+1) h (by rw [hsz])
      have hzero : Work.SSGRoute.UpLctf.mlt (j+1) (Work.SSGRoute.UpLctf.monGrp X h)
          - Ideal.Quotient.mk (fil X (j+1)) (monBrk X h) = 0 := by
        refine Work.SSGRoute.UpLctf.mem_filq_self_eq_zero ?_
        simpa [hsz] using hsub
      have := sub_eq_zero.mp hzero
      simpa [magLT, Work.SSGRoute.UpLctf.mlt] using this
  · refine ⟨1, Subgroup.one_mem _, ?_⟩
    rw [magLT_one, map_zero]
  · rintro b₁ b₂ _ _ ⟨w₁, hw₁, he₁⟩ ⟨w₂, hw₂, he₂⟩
    refine ⟨w₁ * w₂, Subgroup.mul_mem _ hw₁ hw₂, ?_⟩
    rw [magLT_mul X j hj hw₁ hw₂, he₁, he₂, map_add]
  · rintro r b _ ⟨w, hw, he⟩
    rcases lt_or_ge 0 r with hr | hr
    · refine ⟨w ^ r.toNat, Subgroup.pow_mem _ hw _, ?_⟩
      have hr' : ((r.toNat : ℤ)) = r := Int.toNat_of_nonneg (le_of_lt hr)
      rw [magLT_pow X j hj r.toNat hw, he, hr', map_zsmul, zsmul_eq_mul]
    · refine ⟨(w ^ (-r).toNat)⁻¹, Subgroup.inv_mem _ (Subgroup.pow_mem _ hw _), ?_⟩
      have hr'' : (((-r).toNat : ℤ)) = -r := Int.toNat_of_nonneg (by omega)
      rw [magLT_inv X j hj (Subgroup.pow_mem _ hw _), magLT_pow X j hj (-r).toNat hw, he,
        hr'', map_zsmul, zsmul_eq_mul]
      rw [Int.cast_neg, ← neg_mul, neg_neg]

/-- The Magnus leading term of an element of `γ_{j-1}` is invariant under conjugation. -/
theorem magLT_conj {X : Type u} (j : ℕ) (hj : 1 ≤ j) {g u : FreeGroup X}
    (hg : g ∈ gam X (j-1)) :
    magLT X j (u * g * u⁻¹) = magLT X j g := by
  have hconj : u * g * u⁻¹ ∈ gam X (j-1) :=
    Subgroup.Normal.conj_mem (inferInstance : (gam X (j-1)).Normal) g hg u
  have hcomm : ⁅u, g⁆ ∈ gam X j := by
    have h1 : ⁅u, g⁆ ∈ ⁅(⊤ : Subgroup (FreeGroup X)), gam X (j-1)⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top u) hg
    rw [Subgroup.commutator_comm] at h1
    rwa [← Subgroup.lowerCentralSeries_succ (n := j-1), show j - 1 + 1 = j from by omega] at h1
  have hker : magLT X j ⁅u, g⁆ = 0 := magLT_eq_zero_of_mem_succ X j hcomm
  have hprod : magLT X j (u * g * u⁻¹ * g⁻¹) = magLT X j ⁅u, g⁆ := rfl
  have hmul : magLT X j (u * g * u⁻¹ * g⁻¹)
      = magLT X j (u * g * u⁻¹) + magLT X j g⁻¹ := magLT_mul X j hj hconj (Subgroup.inv_mem _ hg)
  rw [← hprod, hmul, magLT_inv X j hj hg] at hker
  exact eq_of_sub_eq_zero (by rw [sub_eq_add_neg]; exact hker)


/-- The length ideal is contained in the length-support submodule. -/
theorem fil_le_filz_sspow (X : Type u) (N : ℕ) : (fil X N : Set (FreeAssoc X)) ⊆ filz X N := by
  rw [fil_eq_filI]
  exact fun a ha => ha

/-! ## The leading term of `γ_{j-1}` lies in the image of the Hall span -/

/-- The normal closure of the weight-`j` monomials is contained in `γ_{j-1}`. -/
theorem normalClosure_monGrpSet_le {X : Type u} [LinearOrder X] (j : ℕ) (hj : 1 ≤ j) :
    Subgroup.normalClosure (Work.SSGRoute.UpLctf.monGrpSet X j) ≤ gam X (j-1) := by
  haveI : (gam X (j-1)).Normal := graded.Gam_normal (G := FreeGroup X) (j - 1)
  refine Subgroup.normalClosure_le_normal ?_
  rintro s ⟨c, hc, rfl⟩
  have h := Work.SSGRoute.UpLctf.monGrp_mem_Gam (X := X) c
  rw [hc] at h
  exact h

/-- The Magnus leading term of an element of the normal closure of the weight-`j` monomials comes
from the Hall span. -/
theorem magLT_mem_normalClosure {X : Type u} [LinearOrder X] (j : ℕ) (hj : 1 ≤ j) {s : FreeGroup X}
    (hs : s ∈ Subgroup.normalClosure (Work.SSGRoute.UpLctf.monGrpSet X j)) :
    ∃ b ∈ hallSpan X j, Ideal.Quotient.mk (fil X (j+1)) b = magLT X j s := by
  classical
  let Good : Subgroup (FreeGroup X) :=
    { carrier := {s | s ∈ gam X (j-1) ∧ ∃ b ∈ hallSpan X j,
        Ideal.Quotient.mk (fil X (j+1)) b = magLT X j s}
      mul_mem' := by
        rintro s t ⟨hsg, b, hb, hbs⟩ ⟨htg, c, hc, hct⟩
        refine ⟨Subgroup.mul_mem _ hsg htg, b + c, Submodule.add_mem _ hb hc, ?_⟩
        rw [magLT_mul X j hj hsg htg, ← hbs, ← hct, map_add]
      one_mem' := by
        refine ⟨Subgroup.one_mem _, 0, Submodule.zero_mem _, ?_⟩
        rw [magLT_one, map_zero]
      inv_mem' := by
        rintro s ⟨hsg, b, hb, hbs⟩
        refine ⟨Subgroup.inv_mem _ hsg, -b, Submodule.neg_mem _ hb, ?_⟩
        rw [magLT_inv X j hj hsg, ← hbs, map_neg] }
  have hnormal : Good.Normal := by
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨hng, b, hb, hbn⟩ := hn
    refine ⟨Subgroup.Normal.conj_mem (inferInstance) n hng g, b, hb, ?_⟩
    rw [magLT_conj (X := X) j hj hng, hbn]
  have hgen : Work.SSGRoute.UpLctf.monGrpSet X j ⊆ (Good : Set (FreeGroup X)) := by
    rintro s ⟨c, hc, rfl⟩
    have hmem : Work.SSGRoute.UpLctf.monGrp X c ∈ gam X (j-1) := by
      have h := Work.SSGRoute.UpLctf.monGrp_mem_Gam (X := X) c
      rw [hc] at h
      exact h
    refine ⟨hmem, monBrk X c, hc ▸ monBrk_mem_hallSpan c, ?_⟩
    have hsub := Work.SSGRoute.UpLctf.mlt_monGrp_sub_mem X (j+1) c (by rw [hc])
    have hzero : Work.SSGRoute.UpLctf.mlt (j+1) (Work.SSGRoute.UpLctf.monGrp X c)
        - Ideal.Quotient.mk (fil X (j+1)) (monBrk X c) = 0 := by
      refine Work.SSGRoute.UpLctf.mem_filq_self_eq_zero ?_
      simpa [hc] using hsub
    have h1 := sub_eq_zero.mp hzero
    simpa [magLT, Work.SSGRoute.UpLctf.mlt] using h1.symm
  have hmem := Subgroup.normalClosure_le_normal hgen hs
  exact (show s ∈ gam X (j-1) ∧ ∃ b ∈ hallSpan X j,
      Ideal.Quotient.mk (fil X (j+1)) b = magLT X j s from hmem).2

/-- The Magnus leading term of an element of `γ_{j-1}` comes from the Hall span. -/
theorem magLT_mem_mkHallSpan {X : Type u} [LinearOrder X] (j : ℕ) (hj : 1 ≤ j) {y : FreeGroup X}
    (hy : y ∈ gam X (j-1)) :
    ∃ b ∈ hallSpan X j, Ideal.Quotient.mk (fil X (j+1)) b = magLT X j y := by
  classical
  haveI : (gam X j).Normal := graded.Gam_normal (G := FreeGroup X) j
  have hy' : y ∈ Subgroup.normalClosure (Work.SSGRoute.UpLctf.monGrpSet X j) ⊔ gam X j := by
    have := Work.SSGRoute.UpLctf.lcs_le_normalClosure_sup X (j-1) hy
    simpa [gam, Work.SSGRoute.UpLctf.Gam, graded.Gam, show j - 1 + 1 = j from by omega] using this
  obtain ⟨s, hs, t, ht, hst⟩ := (Subgroup.mem_sup_of_normal_right
    (s := Subgroup.normalClosure (Work.SSGRoute.UpLctf.monGrpSet X j)) (t := gam X j)).mp hy'
  have hsg : s ∈ gam X (j-1) := normalClosure_monGrpSet_le j hj hs
  have htg : t ∈ gam X (j-1) :=
    Subgroup.lowerCentralSeries_antitone (⊤ : Subgroup (FreeGroup X)) (by omega) ht
  obtain ⟨b, hb, hbeq⟩ := magLT_mem_normalClosure j hj hs
  refine ⟨b, hb, ?_⟩
  rw [← hst, magLT_mul X j hj hsg htg, hbeq, magLT_eq_zero_of_mem_succ X j ht, add_zero]

/-! ## Torsion-freeness of the graded pieces and purity -/

/-- The filtered pieces `filq X N k` (`k ≤ N`) are torsion free. -/
theorem filq_torsion {X : Type u} {N k : ℕ} (hk : k ≤ N) {n : ℤ} (hn : n ≠ 0)
    {z : FreeAssoc X ⧸ fil X N} (hz : z ∈ filq X N k) (h : n • z = 0) : z = 0 := by
  obtain ⟨c, -, hceq⟩ := mem_filq_iff.mp hz
  have hnc : n • c ∈ fil X N := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_zsmul, hceq, h]
  have hnf : n • c ∈ filz X N := fil_le_filz_sspow X N hnc
  have hcz : c ∈ filz X N := by
    rw [mem_filz_iff] at hnf ⊢
    intro w hw
    exact hnf w (by
      rw [MonoidAlgebra.coeff_smul, Finsupp.smul_apply, smul_eq_mul]
      exact mul_ne_zero hn hw)
  rw [← hceq]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (filz_le_fil X N hcz)

/-- Multiplication by a nonzero integer is injective on `filq X N k` for `k ≤ N`. -/
theorem filq_zsmul_injective {X : Type u} {N k : ℕ} (hk : k ≤ N) {n : ℤ} (hn : n ≠ 0)
    {x y : FreeAssoc X ⧸ fil X N} (hx : x ∈ filq X N k) (hy : y ∈ filq X N k)
    (h : n • x = n • y) : x = y :=
  sub_eq_zero.mp (filq_torsion hk hn (Submodule.sub_mem _ hx hy) (by rw [smul_sub, h, sub_self]))

/-- **Purity.**  If the Magnus leading term of `y ∈ γ_{j-1}` is `n` times an element of the
degree-`j` part (`n > 0`), then that element is itself the leading term of an element of
`γ_{j-1}`. -/
theorem purity_aux {X : Type u} [LinearOrder X] (j : ℕ) (hj : 1 ≤ j) (n : ℕ) (hn : 0 < n)
    {y : FreeGroup X} (hy : y ∈ gam X (j-1)) {a : FreeAssoc X ⧸ fil X (j+1)}
    (ha : a ∈ filq X (j+1) j) (h : magLT X j y = ((n : ℤ)) • a) :
    ∃ w ∈ gam X (j-1), magLT X j w = a := by
  classical
  obtain ⟨b₀, hb₀, hb₀eq⟩ := magLT_mem_mkHallSpan j hj hy
  obtain ⟨c, -, hceq⟩ := mem_filq_iff.mp ha
  have hnz : (n : ℤ) ≠ 0 := by exact_mod_cast Nat.pos_iff_ne_zero.mp hn
  have hdiff : b₀ - (n : ℤ) • c ∈ fil X (j+1) := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_zsmul,
      show Ideal.Quotient.mk (fil X (j+1)) b₀ = magLT X j y from hb₀eq, h, hceq, sub_self]
  have hdiv : ∀ w : FreeMonoid X, (n : ℤ) ∣ b₀.coeff w := by
    intro w
    by_cases hw : w.length = j
    · have hf : (b₀ - (n : ℤ) • c) ∈ filz X (j+1) := fil_le_filz_sspow X (j+1) hdiff
      have hzero : (b₀ - (n : ℤ) • c).coeff w = 0 := by
        by_contra hne
        have := (mem_filz_iff.mp hf) w hne
        omega
      have h0 : b₀.coeff w = (n : ℤ) * c.coeff w := by
        rw [MonoidAlgebra.coeff_sub, Finsupp.sub_apply, MonoidAlgebra.coeff_smul,
          Finsupp.smul_apply, smul_eq_mul, sub_eq_zero] at hzero
        exact hzero
      exact ⟨c.coeff w, h0⟩
    · rw [hallSpan_coeff_eq_zero hb₀ hw]
      exact dvd_zero _
  obtain ⟨b, hb, hbeq⟩ := hallSpan_sat j (n : ℤ) hnz b₀ hb₀ hdiv
  have hmb : Ideal.Quotient.mk (fil X (j+1)) b = a := by
    refine filq_zsmul_injective (X := X) (N := j+1) (k := j) (show j ≤ j+1 from by omega) hnz ?_ ha ?_
    · exact Ideal.mem_map_of_mem _ (hallSpan_le_fil j hb)
    · have h1 : (n : ℤ) • (Ideal.Quotient.mk (fil X (j+1)) b)
          = Ideal.Quotient.mk (fil X (j+1)) b₀ := by
        rw [← map_zsmul, ← hbeq]
      rw [h1, hb₀eq, h]
  obtain ⟨w, hw, hweq⟩ := exists_gamma_of_hallSpan j hj hb
  exact ⟨w, hw, by rw [hweq, hmb]⟩



/-- Universe-polymorphic `wtz_filz_exists_pow`. -/
theorem wtz_filz_exists_pow_u {X : Type u} (p : ℕ) (j e : ℕ) (hp : 0 < p)
    {a : Work.SSGRoute.prop5.FreeAssoc X}
    (ha : a ∈ Work.SSGRoute.prop5.wtz p X (j + e))
    (haf : a ∈ Work.SSGRoute.prop5.filz X j) :
    ∃ b ∈ Work.SSGRoute.prop5.filz X j,
      a - ((p : ℤ) ^ e) • b ∈ Work.SSGRoute.prop5.fil X (j + 1) :=
  Work.SSGRoute.prop5.wtz_filz_exists_pow_aux p X j hp e a ha haf

end Work.SSGRoute.Up
