import Mathlib
import Submission.Work.BSW.Char.Setup
import Submission.Work.BSW.Char.sum_chi_t_sq
import Submission.Work.BSW.Char.sum_chi_t_cube_div
import Submission.Work.BSW.Char.chi_t_eq_int

namespace Work.BSW.Char

open OddOrder.RepresentationTheory

/-- An integer whose square is in `[1, 3]` has square `1`: the only squares of integers
that are at most `3` are `0` and `1`. -/
lemma int_sq_le_three {n : ℤ} (h1 : 1 ≤ n ^ 2) (h2 : n ^ 2 ≤ 3) : n ^ 2 = 1 := by
  have hn1 : -1 ≤ n := by
    by_contra h
    push_neg at h
    have h' : n ≤ -2 := by omega
    have : 4 ≤ n ^ 2 := by nlinarith [sq_nonneg (n + 2)]
    omega
  have hn2 : n ≤ 1 := by
    by_contra h
    push_neg at h
    have h' : 2 ≤ n := by omega
    have : 4 ≤ n ^ 2 := by nlinarith [sq_nonneg (n - 2)]
    omega
  have hprod : (n - 1) * (n + 1) ≤ 0 :=
    mul_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  have hle : n ^ 2 ≤ 1 := by nlinarith [hprod]
  omega

/-- **Extraction of the four "unit" characters.**  If `f : ι → ℤ` has `∑_i f i ^ 2 = 4` and
`f i0 = 1`, then `i0` together with exactly three further indices `T` carries all of `f`: on `T`
the values have square `1`, and every nonzero value of `f` occurs at `i0` or in `T`. -/
theorem sq_sum_four_extraction {ι : Type} [Fintype ι] (f : ι → ℤ) (i0 : ι) (hi0 : f i0 = 1)
    (hsum : ∑ i, (f i) ^ 2 = 4) :
    ∃ T : Finset ι, T.card = 3 ∧ i0 ∉ T ∧ (∀ i ∈ T, (f i) ^ 2 = 1) ∧
      (∀ i, f i ≠ 0 → i = i0 ∨ i ∈ T) := by
  classical
  set P : Finset ι := Finset.univ.filter (fun i => f i ≠ 0) with hP
  have hi0P : i0 ∈ P := by
    rw [hP, Finset.mem_filter]
    exact ⟨Finset.mem_univ _, by rw [hi0]; norm_num⟩
  have hPsum : ∑ i ∈ P, (f i) ^ 2 = 4 := by
    have hmain : ∑ i ∈ P, (f i) ^ 2 = ∑ i, (f i) ^ 2 := by
      rw [hP]
      exact Finset.sum_subset (Finset.filter_subset _ _) (by
        intro i _ hi
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_not] at hi
        rw [hi]; ring)
    rw [hmain, hsum]
  have herase : ∑ i ∈ P.erase i0, (f i) ^ 2 = 3 := by
    have h := Finset.sum_erase_add P (fun i => (f i) ^ 2) hi0P
    rw [hPsum, hi0] at h
    norm_num at h
    linarith
  have hone : ∀ i ∈ P.erase i0, (f i) ^ 2 = 1 := by
    intro i hi
    have hne : f i ≠ 0 := by
      have : i ∈ P := Finset.mem_of_mem_erase hi
      rw [hP, Finset.mem_filter] at this
      exact this.2
    have h1 : 1 ≤ (f i) ^ 2 := by
      have hp := sq_pos_of_ne_zero (R := ℤ) hne
      omega
    have h2 : (f i) ^ 2 ≤ 3 := by
      have hs := Finset.single_le_sum (f := fun j => (f j) ^ 2) (fun j _ => sq_nonneg (f j)) hi
      rw [herase] at hs
      exact hs
    exact int_sq_le_three h1 h2
  refine ⟨P.erase i0, ?_, Finset.notMem_erase _ _, hone, ?_⟩
  · have h : ∑ i ∈ P.erase i0, (1 : ℤ) = 3 := by
      rw [← herase]
      exact Finset.sum_congr rfl (fun i hi => (hone i hi).symm)
    have h2 : ∑ i ∈ P.erase i0, (1 : ℤ) = ((P.erase i0).card : ℤ) := by simp
    omega
  · intro i hfi
    by_cases h : i = i0
    · exact Or.inl h
    · right
      rw [Finset.mem_erase]
      exact ⟨h, by rw [hP, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hfi⟩⟩

/-- A nontrivial irreducible character of a finite nonabelian simple group has degree `≥ 2`:
a degree-one irreducible character is a homomorphism `G →* ℂˣ`, hence kills the commutator
subgroup; simplicity forces `⁅G,G⁆` to be `⊥` (making `G` abelian) or `⊤` (making the character
trivial). -/
theorem nontrivial_degree_ge_two {G : Type} [Group G] [Fintype G] (hsimp : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a)
    (χ : OddOrder.RepresentationTheory.IrreducibleCharacter G)
    (hχ : χ ≠ OddOrder.RepresentationTheory.trivialIrreducibleCharacter G)
    (d : ℕ) (hd : (χ : OddOrder.RepresentationTheory.ClassFunction G ℂ) 1 = (d : ℂ)) :
    2 ≤ d := by
  haveI := hsimp
  have key : (χ : ClassFunction G ℂ) 1 = 1 → χ = trivialIrreducibleCharacter G := by
    intro h1
    have hcomm : ∀ n ∈ commutator G, (χ : ClassFunction G ℂ) n = 1 :=
      fun n hn => IsIrreducibleCharacter.apply_eq_one_of_mem_commutator_of_apply_one_eq_one
        χ.isIrreducible h1 hn
    haveI : (commutator G).Normal := Subgroup.commutator_normal ⊤ ⊤
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G) with hbot | htop
    · obtain ⟨a, b, hab⟩ := hnab
      have hcomm' : IsMulCommutative G := (commutator_eq_bot_iff G).mp hbot
      letI := hcomm'
      exact absurd (IsMulCommutative.is_comm.comm a b) hab
    · apply IrreducibleCharacter.ext
      rw [IrreducibleCharacter.coe_trivialIrreducibleCharacter]
      ext g
      rw [trivialClassFunction_apply]
      exact hcomm g (by rw [htop]; exact Subgroup.mem_top g)
  rcases irreducibleCharacter_apply_one_eq_pos_natCast χ with ⟨d', hd'pos, hd'⟩
  have hdd' : d = d' := Nat.cast_injective (by rw [← hd, hd'])
  have hd0 : d ≠ 0 := by omega
  have hd1 : d ≠ 1 := by
    rintro rfl
    rw [Nat.cast_one] at hd
    exact hχ (key hd)
  omega

/-- The sum of `f` over a three-element set `{a, b, c}` is `f a + f b + f c`. -/
lemma sum_three {M α : Type*} [AddCommMonoid M] [DecidableEq α]
    (s : Finset α) (a b c : α) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hs : s = {a, b, c}) (f : α → M) :
    ∑ x ∈ s, f x = f a + f b + f c := by
  subst hs
  rw [Finset.sum_insert (by simp [hab, hac]), Finset.sum_insert (by simp [hbc]),
    Finset.sum_singleton]
  ac_rfl

theorem three_special_characters {G : Type} [Group G] [Fintype G] {t s : G} {K : Subgroup G}
    (h : Work.GW2.BSWHyps2 G t s K) (hk : Nat.card ↥K = 2)
    (hsimp : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a) :
    ∃ χ1 χ2 χ3 : OddOrder.RepresentationTheory.IrreducibleCharacter G, ∃ d1 d2 d3 : ℕ,
      ∃ e1 e2 e3 : ℤ,
      2 ≤ d1 ∧ 2 ≤ d2 ∧ 2 ≤ d3 ∧
      e1 ^ 2 = 1 ∧ e2 ^ 2 = 1 ∧ e3 ^ 2 = 1 ∧
      (χ1 : OddOrder.RepresentationTheory.ClassFunction G ℂ) t = (e1 : ℂ) ∧
      (χ2 : OddOrder.RepresentationTheory.ClassFunction G ℂ) t = (e2 : ℂ) ∧
      (χ3 : OddOrder.RepresentationTheory.ClassFunction G ℂ) t = (e3 : ℂ) ∧
      (χ1 : OddOrder.RepresentationTheory.ClassFunction G ℂ) 1 = (d1 : ℂ) ∧
      (χ2 : OddOrder.RepresentationTheory.ClassFunction G ℂ) 1 = (d2 : ℂ) ∧
      (χ3 : OddOrder.RepresentationTheory.ClassFunction G ℂ) 1 = (d3 : ℂ) ∧
      (1 : ℚ) + e1 / (d1 : ℚ) + e2 / (d2 : ℚ) + e3 / (d3 : ℚ) = 32 / (Nat.card G : ℚ) ∧
      1 + d1 ^ 2 + d2 ^ 2 + d3 ^ 2 ≤ Nat.card G := by
  classical
  have ht : orderOf t = 2 := Work.BSW.orderOf_t h
  have hconj : ∀ x : G, orderOf x = 2 → IsConj x t := Work.BSW.involutions_conj h
  have hcard : Nat.card ↥(Subgroup.centralizer ({t} : Set G)) = 4 :=
    Work.BSW.Api.card_centralizer_of_card_K_two h hk
  have h2sum : ∑ χ : IrreducibleCharacter G, ((χ : ClassFunction G ℂ) t) ^ 2 = 4 :=
    Work.BSW.Char.sum_chi_t_sq ht hconj hcard
  have h3sum : ∑ χ : IrreducibleCharacter G,
      ((χ : ClassFunction G ℂ) t) ^ 3 / ((χ : ClassFunction G ℂ) 1) = 32 / (Nat.card G : ℂ) :=
    Work.BSW.Char.sum_chi_t_cube_div h hk
  have hDsum : ∑ χ : IrreducibleCharacter G, ((χ : ClassFunction G ℂ) 1) ^ 2 = (Nat.card G : ℂ) :=
    OddOrder.RepresentationTheory.sumIrreducibleDegreeSq
  set nv : IrreducibleCharacter G → ℤ :=
    fun χ => Classical.choose (chi_t_eq_int t ht χ) with hnvdef
  have hnv : ∀ χ : IrreducibleCharacter G, (χ : ClassFunction G ℂ) t = (nv χ : ℂ) :=
    fun χ => by simpa [hnvdef] using Classical.choose_spec (chi_t_eq_int t ht χ)
  have hnvsum : ∑ χ : IrreducibleCharacter G, (nv χ) ^ 2 = 4 := by
    have hc : ((∑ χ : IrreducibleCharacter G, (nv χ) ^ 2 : ℤ) : ℂ) = (4 : ℂ) := by
      rw [Int.cast_sum]
      simp only [Int.cast_pow]
      rw [← h2sum]
      exact Finset.sum_congr rfl (fun χ _ => by rw [hnv χ])
    exact Int.cast_injective hc
  have hnvtriv : nv (trivialIrreducibleCharacter G) = 1 := by
    have h1 : ((1 : ℤ) : ℂ) = (nv (trivialIrreducibleCharacter G) : ℂ) := by
      rw [← hnv (trivialIrreducibleCharacter G)]; simp
    exact Int.cast_injective h1.symm
  obtain ⟨T, hTcard, hTnot, hTsq, hTsupp⟩ :=
    sq_sum_four_extraction nv (trivialIrreducibleCharacter G) hnvtriv hnvsum
  obtain ⟨χ1, χ2, χ3, h12, h13, h23, hTeq⟩ := Finset.card_eq_three.mp hTcard
  have hχ1T : χ1 ∈ T := by rw [hTeq]; simp
  have hχ2T : χ2 ∈ T := by rw [hTeq]; simp
  have hχ3T : χ3 ∈ T := by rw [hTeq]; simp
  have hχ1ne : χ1 ≠ trivialIrreducibleCharacter G := fun hh => hTnot (hh ▸ hχ1T)
  have hχ2ne : χ2 ≠ trivialIrreducibleCharacter G := fun hh => hTnot (hh ▸ hχ2T)
  have hχ3ne : χ3 ≠ trivialIrreducibleCharacter G := fun hh => hTnot (hh ▸ hχ3T)
  set deg : IrreducibleCharacter G → ℕ :=
    fun χ => Classical.choose (irreducibleCharacter_apply_one_eq_pos_natCast χ) with hdegdef
  have hdegval : ∀ χ : IrreducibleCharacter G, (χ : ClassFunction G ℂ) 1 = (deg χ : ℂ) :=
    fun χ => (Classical.choose_spec (irreducibleCharacter_apply_one_eq_pos_natCast χ)).2
  have hdegsum : ∑ χ : IrreducibleCharacter G, (deg χ) ^ 2 = Nat.card G := by
    have hc : ((∑ χ : IrreducibleCharacter G, (deg χ) ^ 2 : ℕ) : ℂ) = (Nat.card G : ℂ) := by
      rw [Nat.cast_sum]
      simp only [Nat.cast_pow]
      rw [← hDsum]
      exact Finset.sum_congr rfl (fun χ _ => by rw [hdegval χ])
    exact Nat.cast_injective hc
  have hdegtriv : deg (trivialIrreducibleCharacter G) = 1 := by
    have h1 : ((1 : ℕ) : ℂ) = (deg (trivialIrreducibleCharacter G) : ℂ) := by
      rw [← hdegval (trivialIrreducibleCharacter G)]; simp
    exact Nat.cast_injective h1.symm
  set F : IrreducibleCharacter G → ℂ :=
    fun χ => ((χ : ClassFunction G ℂ) t) ^ 3 / ((χ : ClassFunction G ℂ) 1) with hFdef
  have hFsum : ∑ χ : IrreducibleCharacter G, F χ = 32 / (Nat.card G : ℂ) := by
    simpa [hFdef] using h3sum
  have hsupp : ∀ χ : IrreducibleCharacter G,
      χ ∉ insert (trivialIrreducibleCharacter G) T → F χ = 0 := by
    intro χ hχ
    rw [Finset.mem_insert] at hχ
    have h1 : χ ≠ trivialIrreducibleCharacter G := fun hh => hχ (Or.inl hh)
    have h2 : χ ∉ T := fun hh => hχ (Or.inr hh)
    have hnv0 : nv χ = 0 := by
      by_contra h0
      rcases hTsupp χ h0 with hh | hh
      · exact h1 hh
      · exact h2 hh
    have ht0 : (χ : ClassFunction G ℂ) t = 0 := by rw [hnv χ, hnv0]; simp
    simp only [hFdef]
    rw [ht0]; ring
  have hsplit1 : ∑ χ : IrreducibleCharacter G, F χ =
      ∑ χ ∈ insert (trivialIrreducibleCharacter G) T, F χ :=
    (Finset.sum_subset (Finset.subset_univ _) (fun χ _ hχ => hsupp χ hχ)).symm
  have hsplit2 : ∑ χ ∈ insert (trivialIrreducibleCharacter G) T, F χ =
      F (trivialIrreducibleCharacter G) + ∑ χ ∈ T, F χ :=
    Finset.sum_insert hTnot
  have hTsum : ∑ χ ∈ T, F χ = F χ1 + F χ2 + F χ3 :=
    sum_three T χ1 χ2 χ3 h12 h13 h23 hTeq F
  have hFtriv : F (trivialIrreducibleCharacter G) = 1 := by simp [hFdef]
  have hkey : 1 + F χ1 + F χ2 + F χ3 = 32 / (Nat.card G : ℂ) := by
    have hh := hFsum
    rw [hsplit1, hsplit2, hTsum, hFtriv] at hh
    calc 1 + F χ1 + F χ2 + F χ3 = 1 + (F χ1 + F χ2 + F χ3) := by ring
      _ = 32 / (Nat.card G : ℂ) := hh
  have hcube : ∀ χ ∈ T, (nv χ : ℂ) ^ 3 = (nv χ : ℂ) := by
    intro χ hχ
    have hsq : (nv χ : ℂ) ^ 2 = 1 := by rw [← Int.cast_pow, hTsq χ hχ]; norm_num
    rw [show (nv χ : ℂ) ^ 3 = (nv χ : ℂ) * (nv χ : ℂ) ^ 2 by ring, hsq, mul_one]
  have hFχ1 : F χ1 = (nv χ1 : ℂ) / (deg χ1 : ℂ) := by
    simp only [hFdef]; rw [hnv χ1, hdegval χ1, hcube χ1 hχ1T]
  have hFχ2 : F χ2 = (nv χ2 : ℂ) / (deg χ2 : ℂ) := by
    simp only [hFdef]; rw [hnv χ2, hdegval χ2, hcube χ2 hχ2T]
  have hFχ3 : F χ3 = (nv χ3 : ℂ) / (deg χ3 : ℂ) := by
    simp only [hFdef]; rw [hnv χ3, hdegval χ3, hcube χ3 hχ3T]
  have hQ : (1 : ℚ) + (nv χ1) / (deg χ1 : ℚ) + (nv χ2) / (deg χ2 : ℚ) + (nv χ3) / (deg χ3 : ℚ)
      = 32 / (Nat.card G : ℚ) := by
    refine Rat.cast_injective (α := ℂ) ?_
    push_cast
    rw [← hFχ1, ← hFχ2, ← hFχ3]
    exact hkey
  have hle : ∑ χ ∈ insert (trivialIrreducibleCharacter G) T, (deg χ) ^ 2 ≤ Nat.card G := by
    rw [← hdegsum]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun _ _ _ => Nat.zero_le _)
  rw [Finset.sum_insert hTnot, sum_three T χ1 χ2 χ3 h12 h13 h23 hTeq (fun χ => (deg χ) ^ 2),
    hdegtriv] at hle
  simp only [one_pow] at hle
  have hineq : 1 + (deg χ1) ^ 2 + (deg χ2) ^ 2 + (deg χ3) ^ 2 ≤ Nat.card G := by
    calc 1 + (deg χ1) ^ 2 + (deg χ2) ^ 2 + (deg χ3) ^ 2
        = 1 + ((deg χ1) ^ 2 + (deg χ2) ^ 2 + (deg χ3) ^ 2) := by ring
      _ ≤ Nat.card G := hle
  refine ⟨χ1, χ2, χ3, deg χ1, deg χ2, deg χ3, nv χ1, nv χ2, nv χ3,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hQ, hineq⟩
  · exact nontrivial_degree_ge_two hsimp hnab χ1 hχ1ne (deg χ1) (hdegval χ1)
  · exact nontrivial_degree_ge_two hsimp hnab χ2 hχ2ne (deg χ2) (hdegval χ2)
  · exact nontrivial_degree_ge_two hsimp hnab χ3 hχ3ne (deg χ3) (hdegval χ3)
  · exact hTsq χ1 hχ1T
  · exact hTsq χ2 hχ2T
  · exact hTsq χ3 hχ3T
  · exact hnv χ1
  · exact hnv χ2
  · exact hnv χ3
  · exact hdegval χ1
  · exact hdegval χ2
  · exact hdegval χ3

end Work.BSW.Char
