import Mathlib
import Submission.Work.ShafarevichKoch.GenusAux
import Submission.Work.ShafarevichKoch.card_divisors_filter_le
import Submission.Work.ShafarevichKoch.conjInv_ideal_structure
import Submission.Work.ShafarevichKoch.absNorm_span_sc
import Submission.Work.ShafarevichKoch.absNorm_conjR
import Submission.Work.ShafarevichKoch.eq_one_of_squarefree_mul_sq_eq_sq
import Submission.Work.ShafarevichKoch.norm_int_pos
import Submission.Work.ShafarevichKoch.conjR_mul_self
import Submission.Work.ClassFieldTower.exists_imaginaryQuadratic_classGroupTwoRank_ge_five
import Submission.Work.ClassFieldTower.card_quotient_sq_eq_card_twoTorsion

set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 800000

open scoped Classical
open scoped nonZeroDivisors
open scoped NumberField
open NumberField

noncomputable section

namespace Work.ShafarevichKoch

open Work.ClassFieldTower

/-! ## Genus descent for `Kc = ℚ(√-30030)`

The two facts about the conjugation `conjR` of `𝓞 Kc = ℤ[√-30030]` that the descent uses:

* `I * conjR I` is conjugation-stable and, being also a product of an ideal with its conjugate,
  has square norm, force it to be the principal ideal `(c)` with `c = absNorm I`
  (`mul_map_conjR_eq_span`);
* if `I * I = (α)` then for `γ = conjR α * (α + c)` the ideal `J = (γ) * I` has the same class as
  `I` and is conjugation-stable (`Ideal.map conjR J = J`); the structure theorem for ambiguous
  ideals (`conjInv_ideal_structure`) then writes `J = ⟨c₀·d, c₀·√-30030⟩`, and
  `mk0_span_pair_eq` identifies its class with `mk0Span d hd`. -/

private theorem map_conjR_map_conjR (I : Ideal (𝓞 Kc)) :
    Ideal.map (conjR : 𝓞 Kc →+* 𝓞 Kc) (Ideal.map (conjR : 𝓞 Kc →+* 𝓞 Kc) I) = I := by
  refine le_antisymm ?_ ?_
  · intro z hz
    obtain ⟨y, hy, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ conjR.surjective).mp hz
    obtain ⟨x, hx, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ conjR.surjective).mp hy
    simpa [conjR_invol] using hx
  · intro z hz
    have h1 : conjR z ∈ Ideal.map (conjR : 𝓞 Kc →+* 𝓞 Kc) I := Ideal.mem_map_of_mem _ hz
    have h2 := Ideal.mem_map_of_mem (conjR : 𝓞 Kc →+* 𝓞 Kc) h1
    simpa [conjR_invol] using h2

private theorem isConjInv_mul_map_conjR (I : Ideal (𝓞 Kc)) :
    IsConjInv (I * Ideal.map (conjR : 𝓞 Kc →+* 𝓞 Kc) I) := by
  rw [isConjInv_iff_map_le, Ideal.map_mul, map_conjR_map_conjR, mul_comm]

/-- `I * conjR I` is the principal ideal `(c)` with `c = absNorm I`, for `I ≠ 0`. -/
private theorem mul_map_conjR_eq_span (I : Ideal (𝓞 Kc)) (hI : I ≠ ⊥) :
    ∃ c : ℕ, 0 < c ∧ I * Ideal.map (conjR : 𝓞 Kc →+* 𝓞 Kc) I = Ideal.span {(c : 𝓞 Kc)} := by
  have hσIne : Ideal.map (conjR : 𝓞 Kc →+* 𝓞 Kc) I ≠ ⊥ :=
    fun h => hI ((Ideal.map_eq_bot_iff_of_injective conjR.injective).mp h)
  have hJne : I * Ideal.map (conjR : 𝓞 Kc →+* 𝓞 Kc) I ≠ ⊥ := by
    intro h
    rcases (Ideal.mul_eq_bot.mp h) with h' | h'
    · exact hI h'
    · exact hσIne h'
  obtain ⟨c, d, hc, hd, hJeq⟩ := conjInv_ideal_structure _ hJne (isConjInv_mul_map_conjR I)
  have hnorm1 : Ideal.absNorm (I * Ideal.map (conjR : 𝓞 Kc →+* 𝓞 Kc) I)
      = (Ideal.absNorm I) ^ 2 := by
    rw [map_mul Ideal.absNorm, absNorm_conjR]; ring
  have hnorm2 : Ideal.absNorm (I * Ideal.map (conjR : 𝓞 Kc →+* 𝓞 Kc) I) = c * d * c := by
    rw [hJeq, absNorm_span_sc c d hd]
  have hsquare : d * c ^ 2 = (Ideal.absNorm I) ^ 2 := by
    have h := hnorm1.symm.trans hnorm2
    calc d * c ^ 2 = c * d * c := by ring
      _ = (Ideal.absNorm I) ^ 2 := h.symm
  have hd1 : d = 1 := eq_one_of_squarefree_mul_sq_eq_sq (squarefree_of_dvd_30030 hd) hc.ne' hsquare
  refine ⟨c, hc, ?_⟩
  rw [hJeq, hd1, Nat.mul_one]
  refine le_antisymm ?_ ?_
  · rw [Ideal.span_le]
    rintro z hz
    rcases hz with rfl | rfl
    · exact Ideal.subset_span (Set.mem_singleton (c : 𝓞 Kc))
    · exact Ideal.mul_mem_right scR _ (Ideal.subset_span (Set.mem_singleton (c : 𝓞 Kc)))
  · rw [Ideal.span_le]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact Ideal.subset_span (Set.mem_insert _ _)

/-- **Genus descent.** Every ideal `I ≠ 0` of `𝓞 Kc` whose square is principal has a class of
the form `mk0Span d hd` with `d ∣ 30030`. -/
private theorem exists_mk0Span_eq_of_twoTorsion_aux (I : Ideal (𝓞 Kc)) (hI : I ≠ ⊥)
    (h2 : (I * I).IsPrincipal) :
    ∃ (d : ℕ) (hd : d ∣ 30030),
      ClassGroup.mk0 ⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩ = mk0Span d hd := by
  classical
  obtain ⟨c, hc, hA⟩ := mul_map_conjR_eq_span I hI
  obtain ⟨α, hα⟩ := h2.principal
  have hα' : I * I = Ideal.span ({α} : Set (𝓞 Kc)) := hα
  have hαne : α ≠ 0 := by
    intro h0
    have hbot : I * I = ⊥ := by rw [hα', h0, Ideal.span_singleton_eq_bot]
    rcases (Ideal.mul_eq_bot.mp hbot) with h' | h' <;> exact hI h'
  have hR1 : Ideal.span ({α} : Set (𝓞 Kc)) * Ideal.map (conjR : 𝓞 Kc →+* 𝓞 Kc) I
      = Ideal.span {(c : 𝓞 Kc)} * I := by
    rw [← hα', mul_assoc, hA, mul_comm]
  have hR2 : Ideal.span ({conjR α} : Set (𝓞 Kc)) * I
      = Ideal.span {(c : 𝓞 Kc)} * Ideal.map (conjR : 𝓞 Kc →+* 𝓞 Kc) I := by
    have h := congrArg (Ideal.map (conjR : 𝓞 Kc →+* 𝓞 Kc)) hR1
    simpa [Ideal.map_mul, Ideal.map_span, Set.image_singleton, map_conjR_map_conjR] using h
  have hnormα : Ideal.absNorm (Ideal.span ({α} : Set (𝓞 Kc))) = (Ideal.absNorm I) ^ 2 := by
    rw [← hα', map_mul Ideal.absNorm]; ring
  have hασ : α * conjR α = (c : 𝓞 Kc) * (c : 𝓞 Kc) := by
    have hnat : (Algebra.norm ℤ α).natAbs = (Ideal.absNorm I) ^ 2 := by
      rw [← Ideal.absNorm_span_singleton α]; exact hnormα
    have hcI : (Ideal.absNorm I) ^ 2 = c ^ 2 := by
      have h1 : Ideal.absNorm (I * Ideal.map (conjR : 𝓞 Kc →+* 𝓞 Kc) I)
          = (Ideal.absNorm I) ^ 2 := by
        rw [map_mul Ideal.absNorm, absNorm_conjR]; ring
      have h2' : Ideal.absNorm (I * Ideal.map (conjR : 𝓞 Kc →+* 𝓞 Kc) I) = c ^ 2 := by
        rw [hA, Ideal.absNorm_span_natCast, NumberField.RingOfIntegers.rank, finrank_eq_two]
      rw [← h1, h2']
    have hnn : (0 : ℤ) ≤ Algebra.norm ℤ α := (norm_int_pos α hαne).le
    have hzn : ((Algebra.norm ℤ α).natAbs : ℤ) = Algebra.norm ℤ α := by
      rw [Int.natCast_natAbs, abs_of_nonneg hnn]
    have hcast : ((Algebra.norm ℤ α : ℤ) : 𝓞 Kc)
        = (((Algebra.norm ℤ α).natAbs : ℕ) : 𝓞 Kc) := by
      have h := congrArg (fun m : ℤ => ((m : 𝓞 Kc))) hzn
      rw [Int.cast_natCast] at h
      exact h.symm
    calc α * conjR α = ((Algebra.norm ℤ α : ℤ) : 𝓞 Kc) := conjR_mul_self α
      _ = (((Algebra.norm ℤ α).natAbs : ℕ) : 𝓞 Kc) := hcast
      _ = (((Ideal.absNorm I) ^ 2 : ℕ) : 𝓞 Kc) := by rw [hnat]
      _ = ((c ^ 2 : ℕ) : 𝓞 Kc) := by rw [hcI]
      _ = (c : 𝓞 Kc) * (c : 𝓞 Kc) := by push_cast; ring
  set γ : 𝓞 Kc := conjR α * (α + (c : 𝓞 Kc)) with hγdef
  by_cases hγ0 : γ = 0
  · have hαc : α = -(c : 𝓞 Kc) := by
      have h0 : conjR α * (α + (c : 𝓞 Kc)) = 0 := by rw [← hγdef]; exact hγ0
      have hcα : conjR α ≠ 0 := by
        intro hz
        exact hαne (by simpa [conjR_invol] using congrArg conjR hz)
      have h1 : α + (c : 𝓞 Kc) = 0 := (mul_eq_zero.mp h0).resolve_left hcα
      rw [add_eq_zero_iff_eq_neg] at h1
      exact h1
    have hII : I * I = Ideal.span {(c : 𝓞 Kc)} := by
      rw [hα', hαc, Ideal.span_singleton_neg]
    have hmeq : I * I = I * Ideal.map (conjR : 𝓞 Kc →+* 𝓞 Kc) I := hII.trans hA.symm
    have hstabI : IsConjInv I :=
      (isConjInv_iff_map_le I).mpr (le_of_eq (mul_left_cancel₀ hI hmeq).symm)
    obtain ⟨c₁, d₁, hc₁, hd₁, hIeq⟩ := conjInv_ideal_structure I hI hstabI
    refine ⟨d₁, hd₁, ?_⟩
    have hsub : (⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩ : (Ideal (𝓞 Kc))⁰)
        = ⟨Ideal.span ({↑(c₁ * d₁), (↑c₁ : 𝓞 Kc) * scR} : Set (𝓞 Kc)),
            mem_nonZeroDivisors_of_ne_zero (by rw [← hIeq]; exact hI)⟩ := Subtype.ext hIeq
    rw [hsub]
    exact mk0_span_pair_eq c₁ d₁ hc₁.ne' hd₁ _
  · have hspanγne : Ideal.span ({γ} : Set (𝓞 Kc)) ≠ ⊥ := by
      intro h
      exact hγ0 (Ideal.span_singleton_eq_bot.mp h)
    set Jv : (Ideal (𝓞 Kc))⁰ :=
      ⟨Ideal.span ({γ} : Set (𝓞 Kc)), mem_nonZeroDivisors_of_ne_zero hspanγne⟩
        * ⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩ with hJvdef
    set J : Ideal (𝓞 Kc) := (Jv : Ideal (𝓞 Kc)) with hJdef
    have hJne : J ≠ ⊥ := by
      intro h
      rcases (Ideal.mul_eq_bot.mp h) with h' | h'
      · exact hspanγne h'
      · exact hI h'
    have hconjγ : conjR γ = α * (conjR α + (c : 𝓞 Kc)) := by
      rw [hγdef]
      simp only [map_mul, map_add, conjR_invol, map_natCast]
    have hone1 : Ideal.span ({α * (conjR α + (c : 𝓞 Kc))} : Set (𝓞 Kc))
        = Ideal.span {(c : 𝓞 Kc)} * Ideal.span ({α + (c : 𝓞 Kc)} : Set (𝓞 Kc)) := by
      rw [Ideal.span_singleton_mul_span_singleton]
      congr 1
      rw [mul_add, mul_add, hασ]
      ring
    have hone2 : Ideal.span ({conjR α * (α + (c : 𝓞 Kc))} : Set (𝓞 Kc))
        = Ideal.span ({conjR α} : Set (𝓞 Kc))
          * Ideal.span ({α + (c : 𝓞 Kc)} : Set (𝓞 Kc)) := by
      rw [Ideal.span_singleton_mul_span_singleton]
    have hstable : Ideal.map (conjR : 𝓞 Kc →+* 𝓞 Kc) J = J := by
      show Ideal.map (conjR : 𝓞 Kc →+* 𝓞 Kc) (Ideal.span ({γ} : Set (𝓞 Kc)) * I)
        = Ideal.span ({γ} : Set (𝓞 Kc)) * I
      rw [Ideal.map_mul, Ideal.map_span, Set.image_singleton]
      change Ideal.span ({conjR γ} : Set (𝓞 Kc)) * Ideal.map (conjR : 𝓞 Kc →+* 𝓞 Kc) I
        = Ideal.span ({γ} : Set (𝓞 Kc)) * I
      rw [hconjγ, hone1]
      conv_rhs => rw [hγdef, hone2]
      rw [mul_comm (Ideal.span {(c : 𝓞 Kc)}) (Ideal.span ({α + (c : 𝓞 Kc)} : Set (𝓞 Kc)))]
      rw [mul_assoc, ← hR2]
      ring_nf
    have hstabJ : IsConjInv J := (isConjInv_iff_map_le J).mpr (le_of_eq hstable)
    obtain ⟨c₂, d₂, hc₂, hd₂, hJeq2⟩ := conjInv_ideal_structure J hJne hstabJ
    refine ⟨d₂, hd₂, ?_⟩
    have hmkJ : ClassGroup.mk0 ⟨J, mem_nonZeroDivisors_of_ne_zero hJne⟩
        = ClassGroup.mk0 ⟨I, mem_nonZeroDivisors_of_ne_zero hI⟩ := by
      have hval : (⟨J, mem_nonZeroDivisors_of_ne_zero hJne⟩ : (Ideal (𝓞 Kc))⁰) = Jv :=
        Subtype.ext rfl
      rw [hval, hJvdef, map_mul]
      have hone : ClassGroup.mk0 ⟨Ideal.span ({γ} : Set (𝓞 Kc)),
          mem_nonZeroDivisors_of_ne_zero hspanγne⟩ = 1 := by
        refine (ClassGroup.mk0_eq_one_iff _).mpr ?_
        exact Submodule.IsPrincipal.mk ⟨γ, rfl⟩
      rw [hone, one_mul]
    rw [← hmkJ]
    have hsub2 : (⟨J, mem_nonZeroDivisors_of_ne_zero hJne⟩ : (Ideal (𝓞 Kc))⁰)
        = ⟨Ideal.span ({↑(c₂ * d₂), (↑c₂ : 𝓞 Kc) * scR} : Set (𝓞 Kc)),
            mem_nonZeroDivisors_of_ne_zero (by rw [← hJeq2]; exact hJne)⟩ := Subtype.ext hJeq2
    rw [hsub2]
    exact mk0_span_pair_eq c₂ d₂ hc₂.ne' hd₂ _

/-- The `2`-torsion of the class group of `Kc = ℚ(√-30030)` has at most `32 = 2^5` elements,
i.e. `rank₂ Cl(Kc) ≤ 5` (genus theory: the `2`-torsion classes are the classes of
`⟨d, √-30030⟩` for `d ∣ 30030`, and `d` and `30030/d` give the same class, so only the `32`
divisors of `30030` that are `≤ 173` matter).

Ingredients: `mk0Span`, `mk0Span_compl` (`[⟨d, scR⟩] = [⟨30030/d, scR⟩]`) from `GenusAux`,
`card_divisors_filter_le` (`((30030 : ℕ).divisors.filter (· ≤ 173)).card = 32`), and
`exists_mk0Span_eq_of_twoTorsion` (for an ideal `I ≠ 0` with `(I * I).IsPrincipal` there is
`d ∣ 30030` with `ClassGroup.mk0 ⟨I,_⟩ = mk0Span d hd`; the class group is generated by integral
ideals, e.g. `ClassGroup.mk0_surjective`, and `[I]² = 1` gives `(I * I).IsPrincipal` via
`ClassGroup.mk0_eq_one_iff`).

Route: let `S := (30030).divisors.filter (· ≤ 173)` and
`f : {d // d ∈ S} → ClassGroup (𝓞 Kc)`, `f d = mk0Span d.val (Nat.dvd_of_mem_divisors ...)`.
Show `Set.range f` contains every `x` with `x ^ 2 = 1`: pick `I` with `mk0 I = x`, apply the genus
descent to get `d ∣ 30030` with `x = mk0Span d hd`, and replace `d` by `30030/d` if `173 < d`
(`mk0Span_compl`), noting `d ∈ (30030).divisors` and `173 < d` implies `30030/d ≤ 173` (from
`30030 < 174 * d` and `Nat.div_lt_iff_lt_mul`).  Then
`Nat.card {x // x ^ 2 = 1} ≤ Nat.card (Set.range f) ≤ Nat.card {d // d ∈ S} = S.card = 32`, via
`Nat.card_le_card_of_injective` (the inclusion of `{x // x^2 = 1}` into `Set.range f`) and
`Nat.card_le_card_of_surjective` (for the surjection `{d // d ∈ S} → Set.range f`) together with
`Fintype.card_coe`. -/
theorem card_twoTorsion_le_32 :
    Nat.card {x : ClassGroup (NumberField.RingOfIntegers Work.ClassFieldTower.Kc) // x ^ 2 = 1}
      ≤ 32 := by
  classical
  set S : Finset ℕ := (30030 : ℕ).divisors.filter (· ≤ 173) with hS
  have hScard : S.card = 32 := card_divisors_filter_le
  let f : {d : ℕ // d ∈ S} → ClassGroup (𝓞 Kc) :=
    fun d => mk0Span d.1 (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp d.2).1)
  have hrange : ∀ x : ClassGroup (𝓞 Kc), x ^ 2 = 1 → x ∈ Set.range f := by
    intro x hx
    obtain ⟨J, hJ⟩ := ClassGroup.mk0_surjective x
    set I : Ideal (𝓞 Kc) := (J : Ideal (𝓞 Kc)) with hIdef
    have hIne : I ≠ ⊥ := by
      intro h
      exact (mem_nonZeroDivisors_iff_ne_zero.mp J.2) h
    have hJsub : (⟨I, mem_nonZeroDivisors_of_ne_zero hIne⟩ : (Ideal (𝓞 Kc))⁰) = J :=
      Subtype.ext rfl
    have hxI : ClassGroup.mk0 ⟨I, mem_nonZeroDivisors_of_ne_zero hIne⟩ = x := by
      rw [hJsub]; exact hJ
    have hIIne : I * I ≠ ⊥ := by
      intro h
      rcases (Ideal.mul_eq_bot.mp h) with h' | h'
      · exact hIne h'
      · exact hIne h'
    have h2 : (I * I).IsPrincipal := by
      have hJJ : ClassGroup.mk0 ⟨I * I, mem_nonZeroDivisors_of_ne_zero hIIne⟩ = 1 := by
        have hsub : (⟨I * I, mem_nonZeroDivisors_of_ne_zero hIIne⟩ : (Ideal (𝓞 Kc))⁰) = J * J :=
          Subtype.ext rfl
        rw [hsub, map_mul, hJ]
        rw [← pow_two, hx]
      exact (ClassGroup.mk0_eq_one_iff _).mp hJJ
    obtain ⟨d, hd, hdclass⟩ := exists_mk0Span_eq_of_twoTorsion_aux I hIne h2
    have hxclass : x = mk0Span d hd := by rw [← hxI, hdclass]
    by_cases h : d ≤ 173
    · refine ⟨⟨d, ?_⟩, ?_⟩
      · exact Finset.mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hd, by norm_num⟩, h⟩
      · rw [hxclass]
    · have hle' : 30030 / d ≤ 173 := by
        by_contra hle
        push Not at hle
        have hlt : 173 < d := lt_of_not_ge h
        have hmul : 30030 / d * d = 30030 := Nat.div_mul_cancel hd
        have hbig : 174 * 174 ≤ (30030 / d) * d :=
          Nat.mul_le_mul (by omega) (by omega)
        rw [hmul] at hbig
        omega
      refine ⟨⟨30030 / d, ?_⟩, ?_⟩
      · exact Finset.mem_filter.mpr
          ⟨Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd hd, by norm_num⟩, hle'⟩
      · rw [hxclass]
        exact (mk0Span_compl d hd).symm
  have h1 : Nat.card {x : ClassGroup (𝓞 Kc) // x ^ 2 = 1} ≤ Nat.card (Set.range f) :=
    Nat.card_le_card_of_injective (fun x => (⟨x.1, hrange x.1 x.2⟩ : Set.range f))
      (by
        intro a b hab
        exact Subtype.ext (congrArg (fun z : Set.range f => (z : ClassGroup (𝓞 Kc))) hab))
  have h2 : Nat.card (Set.range f) ≤ Nat.card {d : ℕ // d ∈ S} :=
    Nat.card_le_card_of_surjective (fun d => (⟨f d, Set.mem_range_self d⟩ : Set.range f))
      (by
        intro y
        obtain ⟨d, hd⟩ := y.2
        exact ⟨d, Subtype.ext hd⟩)
  have h3 : Nat.card {d : ℕ // d ∈ S} = 32 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe, hScard]
  exact le_trans h1 (le_trans h2 (le_of_eq h3))

end Work.ShafarevichKoch
