import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.MinkDefs
import Submission.Work.HP.box_card

set_option autoImplicit false

noncomputable section

open Finset
open scoped BigOperators

namespace Work.HP.ESL

open Work.HP

/-- Coordinate bound: each coordinate of an integer vector is at most its Euclidean norm. -/
lemma eNorm_coord_le {ι : Type*} [Fintype ι] (v : ι → ℤ) (i : ι) :
    |((v i : ℤ) : ℝ)| ≤ eNorm v := by
  rw [eNorm]
  rw [← Real.sqrt_sq_eq_abs (v i : ℝ)]
  apply Real.sqrt_le_sqrt
  exact Finset.single_le_sum (fun j _ => sq_nonneg ((v j : ℤ) : ℝ)) (Finset.mem_univ i)

/-- Each coordinate of a vector of norm at most `R` is at most `⌈R⌉₊` in absolute value. -/
lemma coord_abs_le_ceil {ι : Type*} [Fintype ι] (v : ι → ℤ) {R : ℝ} (hv : eNorm v ≤ R) (i : ι) :
    |v i| ≤ (⌈R⌉₊ : ℤ) := by
  have hc : |((v i : ℤ) : ℝ)| ≤ eNorm v := eNorm_coord_le v i
  have h1 : |((v i : ℤ) : ℝ)| ≤ R := le_trans hc hv
  have h2 : ((|v i| : ℤ) : ℝ) ≤ R := by
    rw [← Int.cast_abs] at h1; exact h1
  have h3 : R ≤ ((⌈R⌉₊ : ℕ) : ℝ) := Nat.le_ceil R
  have h4 : ((|v i| : ℤ) : ℝ) ≤ ((⌈R⌉₊ : ℕ) : ℝ) := le_trans h2 h3
  exact_mod_cast h4

/-- From a nonzero coordinate of `c`, the Euclidean norm of `c` is at least one. -/
lemma one_le_eNorm_of_ne {ι : Type*} [Fintype ι] (c : ι → ℤ) (i : ι) (hi : c i ≠ 0) :
    1 ≤ eNorm c := by
  have h1 : (1:ℤ) ≤ |c i| := Int.one_le_abs hi
  have h2 : (1:ℝ) ≤ ((|c i| : ℤ) : ℝ) := by exact_mod_cast h1
  have h3 : ((|c i| : ℤ) : ℝ) ≤ eNorm c := by
    rw [Int.cast_abs]; exact eNorm_coord_le c i
  exact le_trans h2 h3

/-- Counting the integers `t` with `|a·t + s| ≤ M` when `a ≠ 0` and `M ≥ 0`:
an interval of reals of length `2M/|a|` contains at most `2M/|a| + 1` integers. -/
lemma card_int_slab {a s : ℤ} (ha : a ≠ 0) {M : ℝ} (hM : 0 ≤ M) (T : Finset ℤ)
    (hT : ∀ t ∈ T, |(((a * t + s : ℤ)) : ℝ)| ≤ M) :
    (T.card : ℝ) ≤ 2 * M / |((a : ℤ) : ℝ)| + 1 := by
  rcases T.eq_empty_or_nonempty with rfl | hne
  · simp only [Finset.card_empty, Nat.cast_zero]
    have h : 0 ≤ 2 * M / |((a : ℤ) : ℝ)| := div_nonneg (by linarith) (abs_nonneg _)
    linarith
  · set n := T.min' hne with hn_def
    set m := T.max' hne with hm_def
    have hn : n ∈ T := T.min'_mem hne
    have hm : m ∈ T := T.max'_mem hne
    have hnm : n ≤ m := T.min'_le m hm
    have hapos : 0 < |((a : ℤ) : ℝ)| := abs_pos.mpr (by exact_mod_cast ha)
    have hcard : (T.card : ℝ) ≤ ((m - n : ℤ) : ℝ) + 1 := by
      have hsub : T ⊆ Finset.Icc n m := fun t ht =>
        Finset.mem_Icc.mpr ⟨T.min'_le t ht, T.le_max' t ht⟩
      have h1 : (T.card : ℤ) ≤ ((Finset.Icc n m).card : ℤ) := by
        exact_mod_cast Finset.card_le_card hsub
      rw [Int.card_Icc_of_le n m (by omega)] at h1
      calc (T.card : ℝ) ≤ ((m + 1 - n : ℤ) : ℝ) := by exact_mod_cast h1
        _ = ((m - n : ℤ) : ℝ) + 1 := by push_cast; ring
    have hgap : ((m - n : ℤ) : ℝ) * |((a : ℤ) : ℝ)| ≤ 2 * M := by
      have hm' := hT m hm
      have hn' := hT n hn
      have key : (((a * (m - n) : ℤ)) : ℝ) =
          ((a * m + s : ℤ) : ℝ) - ((a * n + s : ℤ) : ℝ) := by push_cast; ring
      have h2 : |(((a * (m - n) : ℤ)) : ℝ)| ≤ 2 * M := by
        rw [key]
        calc |((a * m + s : ℤ) : ℝ) - ((a * n + s : ℤ) : ℝ)|
            ≤ |((a * m + s : ℤ) : ℝ)| + |((a * n + s : ℤ) : ℝ)| := abs_sub _ _
          _ ≤ M + M := add_le_add hm' hn'
          _ = 2 * M := by ring
      have hmnn : (0:ℝ) ≤ ((m - n : ℤ) : ℝ) := by
        have : (0:ℤ) ≤ m - n := by omega
        exact_mod_cast this
      have habs : |(((a * (m - n) : ℤ)) : ℝ)| = ((m - n : ℤ) : ℝ) * |((a : ℤ) : ℝ)| := by
        rw [show (((a * (m - n) : ℤ)) : ℝ) =
            ((a : ℤ) : ℝ) * ((m - n : ℤ) : ℝ) by push_cast; ring]
        rw [abs_mul, abs_of_nonneg hmnn, mul_comm]
      rw [habs] at h2
      exact h2
    have hmn2 : ((m - n : ℤ) : ℝ) ≤ 2 * M / |((a : ℤ) : ℝ)| := by
      rw [le_div_iff₀ hapos]
      exact hgap
    linarith

/-- If `c ≠ 0` there is a coordinate `i₀` with `c i₀ ≠ 0` and
`‖c‖² ≤ #ι · (c i₀)²`, i.e. `|c i₀| ≥ ‖c‖/√#ι`. -/
lemma exists_max_coord {ι : Type*} [Fintype ι] (c : ι → ℤ) (hc : c ≠ 0) :
    ∃ i₀, c i₀ ≠ 0 ∧ eNorm c ^ 2 ≤ (Fintype.card ι : ℝ) * ((c i₀ : ℤ) : ℝ)^2 := by
  have hne : (Finset.univ : Finset ι).Nonempty := by
    rw [Finset.univ_nonempty_iff]
    by_contra h
    apply hc
    funext i
    exact (h ⟨i⟩).elim
  obtain ⟨i₀, -, hi₀⟩ := Finset.exists_max_image (Finset.univ : Finset ι)
      (fun i => ((c i : ℤ) : ℝ)^2) hne
  refine ⟨i₀, ?_, ?_⟩
  · intro h0
    apply hc
    funext i
    have hz : ((c i₀ : ℤ) : ℝ)^2 = 0 := by rw [h0]; norm_num
    have hle : ((c i : ℤ) : ℝ)^2 ≤ 0 := by rw [← hz]; exact hi₀ i (Finset.mem_univ i)
    have hci : ((c i : ℤ) : ℝ) = 0 :=
      pow_eq_zero_iff (n := 2) (by norm_num) |>.mp (le_antisymm hle (sq_nonneg _))
    exact_mod_cast hci
  · rw [eNorm_sq_eq]
    have hdot : ((dotZ c c : ℤ) : ℝ) = ∑ i, ((c i : ℤ) : ℝ)^2 := by
      rw [dotZ_apply]; push_cast
      exact Finset.sum_congr rfl (fun i _ => by ring)
    rw [hdot]
    calc ∑ i, ((c i : ℤ) : ℝ)^2 ≤ ∑ _i : ι, ((c i₀ : ℤ) : ℝ)^2 :=
          Finset.sum_le_sum (fun i _ => hi₀ i (Finset.mem_univ i))
      _ = (Fintype.card ι : ℝ) * ((c i₀ : ℤ) : ℝ)^2 := by
          rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- Cardinality of the coordinate box on the coordinates different from `i₀`. -/
lemma box_card_subtype {ι : Type*} [Fintype ι] [DecidableEq ι] (i₀ : ι) (B : ℕ) :
    ((Fintype.piFinset (fun _ : {j : ι // j ≠ i₀} => Finset.Icc (-(B:ℤ)) (B:ℤ))).card : ℝ)
      = (2 * (B : ℝ) + 1) ^ (Fintype.card ι - 1) := by
  rw [(box_card (ι := {j : ι // j ≠ i₀}) B).1]
  have h : Fintype.card {j : ι // j ≠ i₀} = Fintype.card ι - 1 := by
    have hh := Fintype.card_subtype_compl (fun j : ι => j = i₀)
    rw [hh, Fintype.card_subtype_eq]
  rw [h]

/-- In every fibre of the coordinate projection away from `i₀`, the slab condition
`|⟨c,v⟩| ≤ M` bounds the number of possible values of the `i₀`-coordinate by
`2M/|c i₀| + 1`. -/
lemma fiber_card_le {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → ℤ) (i₀ : ι)
    (hca : c i₀ ≠ 0) (R : ℝ) (b : {j : ι // j ≠ i₀} → ℤ) (s : Finset (ι → ℤ))
    (hs : ∀ v ∈ s, |((dotZ c v : ℤ) : ℝ)| ≤ eNorm c ^ 2 / 2 ∧ eNorm v ≤ R)
    (hb : ∀ v ∈ s, ∀ j : {j : ι // j ≠ i₀}, v j.1 = b j) :
    (s.card : ℝ) ≤ 2 * (eNorm c ^ 2 / 2) / |((c i₀ : ℤ) : ℝ)| + 1 := by
  set S : ℤ := ∑ j : {j : ι // j ≠ i₀}, c j.1 * b j with hS
  have hsum : ∀ v ∈ s, dotZ c v = c i₀ * v i₀ + S := by
    intro v hv
    rw [dotZ_apply]
    rw [← Finset.sum_erase_add (Finset.univ) (fun i => c i * v i) (Finset.mem_univ i₀)]
    have hmid : (∑ x ∈ Finset.univ.erase i₀, c x * v x) = S := by
      rw [hS]
      rw [Finset.sum_subtype (Finset.univ.erase i₀) (p := fun x => x ≠ i₀)
        (fun x => by simp only [Finset.mem_erase, Finset.mem_univ, and_true])
        (fun i => c i * v i)]
      exact Finset.sum_congr rfl (fun j _ => by rw [hb v hv j])
    rw [hmid, add_comm]
  set T : Finset ℤ := s.image (fun v => v i₀) with hT'
  have hinj : Set.InjOn (fun v : ι → ℤ => v i₀) ↑s := by
    intro u hu w hw heq
    funext i
    by_cases h : i = i₀
    · rw [h]; exact heq
    · rw [hb u hu ⟨i, h⟩, hb w hw ⟨i, h⟩]
  have hcard : T.card = s.card := Finset.card_image_of_injOn hinj
  have hT : ∀ t ∈ T, |(((c i₀ * t + S : ℤ)) : ℝ)| ≤ eNorm c ^ 2 / 2 := by
    intro t ht
    rw [Finset.mem_image] at ht
    obtain ⟨v, hv, rfl⟩ := ht
    rw [← hsum v hv]
    exact (hs v hv).1
  have h := card_int_slab hca (M := eNorm c ^ 2 / 2) (by positivity) T hT
  rwa [hcard] at h

/-- Arithmetic comparison: `2·(‖c‖²/2)/|c i₀| + 1 ≤ (√#ι + 1)·‖c‖`. -/
lemma slab_arith {ι : Type*} [Fintype ι] (c : ι → ℤ) (i₀ : ι)
    (hca : ((c i₀ : ℤ) : ℝ) ≠ 0)
    (hmax : eNorm c ^ 2 ≤ (Fintype.card ι : ℝ) * ((c i₀ : ℤ) : ℝ)^2)
    (hge : 1 ≤ eNorm c) :
    2 * (eNorm c ^ 2 / 2) / |((c i₀ : ℤ) : ℝ)| + 1
      ≤ (Real.sqrt (Fintype.card ι) + 1) * eNorm c := by
  have ha : 0 < |((c i₀ : ℤ) : ℝ)| := abs_pos.mpr hca
  have h2 : eNorm c ^ 2 / |((c i₀ : ℤ) : ℝ)| ≤ Real.sqrt (Fintype.card ι) * eNorm c := by
    have ht2 : (eNorm c / |((c i₀ : ℤ) : ℝ)|)^2 ≤ (Fintype.card ι : ℝ) := by
      rw [div_pow, div_le_iff₀ (by positivity : (0:ℝ) < |((c i₀ : ℤ) : ℝ)|^2)]
      rw [sq_abs]
      exact hmax
    have ht : eNorm c / |((c i₀ : ℤ) : ℝ)| ≤ Real.sqrt (Fintype.card ι) := by
      rw [← Real.sqrt_sq (div_nonneg (eNorm_nonneg c) (abs_nonneg _))]
      exact Real.sqrt_le_sqrt ht2
    have heq : eNorm c ^ 2 / |((c i₀ : ℤ) : ℝ)| =
        eNorm c * (eNorm c / |((c i₀ : ℤ) : ℝ)|) := by field_simp
    rw [heq, mul_comm (Real.sqrt (Fintype.card ι)) (eNorm c)]
    exact mul_le_mul_of_nonneg_left ht (eNorm_nonneg c)
  calc 2 * (eNorm c ^ 2 / 2) / |((c i₀ : ℤ) : ℝ)| + 1
      = eNorm c ^ 2 / |((c i₀ : ℤ) : ℝ)| + 1 := by ring
    _ ≤ Real.sqrt (Fintype.card ι) * eNorm c + 1 := by linarith
    _ ≤ Real.sqrt (Fintype.card ι) * eNorm c + eNorm c := by linarith
    _ = (Real.sqrt (Fintype.card ι) + 1) * eNorm c := by ring

/-- The coordinate box on the index set `{j // j ≠ i₀}`. -/
def coordBox {ι : Type*} [Fintype ι] [DecidableEq ι] (i₀ : ι) (B : ℕ) :
    Finset ({j : ι // j ≠ i₀} → ℤ) :=
  Fintype.piFinset (fun _ : {j : ι // j ≠ i₀} => Finset.Icc (-(B:ℤ)) (B:ℤ))

lemma mem_coordBox {ι : Type*} [Fintype ι] [DecidableEq ι] {i₀ : ι} {B : ℕ}
    {v : {j : ι // j ≠ i₀} → ℤ} :
    v ∈ coordBox i₀ B ↔ ∀ j, v j ∈ Finset.Icc (-(B:ℤ)) (B:ℤ) := by
  rw [coordBox, Fintype.mem_piFinset]

lemma coordBox_card {ι : Type*} [Fintype ι] [DecidableEq ι] (i₀ : ι) (B : ℕ) :
    ((coordBox i₀ B).card : ℝ) = (2 * (B : ℝ) + 1) ^ (Fintype.card ι - 1) := by
  rw [coordBox]; exact box_card_subtype i₀ B

theorem slab_ball_ncard {ι : Type*} [Fintype ι] [DecidableEq ι] (c : ι → ℤ) (hc : c ≠ 0) (R : ℝ) :
    ((({v : ι → ℤ | |((dotZ c v : ℤ) : ℝ)| ≤ eNorm c ^ 2 / 2 ∧ eNorm v ≤ R} :
        Set (ι → ℤ)).ncard : ℝ))
      ≤ (Real.sqrt (Fintype.card ι) + 1) * eNorm c
          * (2 * ((⌈R⌉₊ : ℕ) : ℝ) + 1) ^ (Fintype.card ι - 1) := by
  classical
  set S : Set (ι → ℤ) :=
    {v : ι → ℤ | |((dotZ c v : ℤ) : ℝ)| ≤ eNorm c ^ 2 / 2 ∧ eNorm v ≤ R} with hS
  obtain ⟨i₀, hi₀ne, hmax⟩ := exists_max_coord c hc
  have hge : 1 ≤ eNorm c := one_le_eNorm_of_ne c i₀ hi₀ne
  have hcaR : ((c i₀ : ℤ) : ℝ) ≠ 0 := fun h => hi₀ne (by exact_mod_cast h)
  -- finiteness of `S` from the full coordinate box
  have hSsub : S ⊆ ↑(Fintype.piFinset (fun _ : ι => Finset.Icc (-(⌈R⌉₊:ℤ)) (⌈R⌉₊:ℤ))) := by
    intro v hv
    rw [hS] at hv
    rw [Finset.mem_coe, Fintype.mem_piFinset]
    intro i
    exact Finset.mem_Icc.mpr (abs_le.mp (coord_abs_le_ceil v hv.2 i))
  have hfin : S.Finite := Set.Finite.subset (Finset.finite_toSet _) hSsub
  rw [Set.ncard_eq_toFinset_card S hfin]
  have hmap : Set.MapsTo (fun v : ι → ℤ => fun j : {j : ι // j ≠ i₀} => v j.1)
      ↑(hfin.toFinset) ↑(coordBox i₀ ⌈R⌉₊) := by
    intro v hv
    rw [Set.Finite.coe_toFinset hfin] at hv
    rw [hS] at hv
    rw [Finset.mem_coe, mem_coordBox]
    intro j
    exact Finset.mem_Icc.mpr (abs_le.mp (coord_abs_le_ceil v hv.2 j.1))
  have hN : ∀ b ∈ coordBox i₀ ⌈R⌉₊,
      ((hfin.toFinset.filter
        (fun v => (fun v : ι → ℤ => fun j : {j : ι // j ≠ i₀} => v j.1) v = b)).card : ℝ)
        ≤ 2 * (eNorm c ^ 2 / 2) / |((c i₀ : ℤ) : ℝ)| + 1 := by
    intro b hb
    refine fiber_card_le c i₀ hi₀ne R b _ ?_ ?_
    · intro v hv
      rw [Finset.mem_filter] at hv
      have hvS : v ∈ S := by
        have h1 : v ∈ (hfin.toFinset : Set (ι → ℤ)) := hv.1
        rwa [Set.Finite.coe_toFinset hfin] at h1
      rw [hS] at hvS
      exact hvS
    · intro v hv j
      rw [Finset.mem_filter] at hv
      exact congrFun hv.2 j
  have hsum : ((hfin.toFinset.card : ℕ) : ℝ)
      ≤ ((coordBox i₀ ⌈R⌉₊).card : ℝ)
        * (2 * (eNorm c ^ 2 / 2) / |((c i₀ : ℤ) : ℝ)| + 1) := by
    rw [Finset.card_eq_sum_card_fiberwise hmap]
    push_cast
    calc (∑ b ∈ coordBox i₀ ⌈R⌉₊, ((hfin.toFinset.filter
            (fun v => (fun v : ι → ℤ => fun j : {j : ι // j ≠ i₀} => v j.1) v = b)).card : ℕ) : ℝ)
        = ∑ b ∈ coordBox i₀ ⌈R⌉₊, ((hfin.toFinset.filter
            (fun v => (fun v : ι → ℤ => fun j : {j : ι // j ≠ i₀} => v j.1) v = b)).card : ℝ) := by
          push_cast; rfl
      _ ≤ ∑ _b ∈ coordBox i₀ ⌈R⌉₊,
            (2 * (eNorm c ^ 2 / 2) / |((c i₀ : ℤ) : ℝ)| + 1) :=
          Finset.sum_le_sum fun b hb => hN b hb
      _ = ((coordBox i₀ ⌈R⌉₊).card : ℝ)
            * (2 * (eNorm c ^ 2 / 2) / |((c i₀ : ℤ) : ℝ)| + 1) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  calc ((hfin.toFinset.card : ℕ) : ℝ)
      ≤ ((coordBox i₀ ⌈R⌉₊).card : ℝ)
        * (2 * (eNorm c ^ 2 / 2) / |((c i₀ : ℤ) : ℝ)| + 1) := hsum
    _ ≤ ((coordBox i₀ ⌈R⌉₊).card : ℝ) * ((Real.sqrt (Fintype.card ι) + 1) * eNorm c) :=
        mul_le_mul_of_nonneg_left (slab_arith c i₀ hcaR hmax hge) (Nat.cast_nonneg _)
    _ = (Real.sqrt (Fintype.card ι) + 1) * eNorm c
          * (2 * ((⌈R⌉₊ : ℕ) : ℝ) + 1) ^ (Fintype.card ι - 1) := by
        rw [coordBox_card]; ring

end Work.HP.ESL
