import Mathlib
import Submission.Work.HP.DNC.shifted_card_div_pow_tendsto

set_option autoImplicit false
noncomputable section

open Filter MeasureTheory Finset Bornology
open scoped Pointwise Topology

namespace Work.HP.DNC

variable {ι : Type*} [Fintype ι]

/-- The lattice points of a bounded set form a finite set. -/
private lemma finite_latticePoints_of_isBounded {B : Set (ι → ℝ)} (hB : Bornology.IsBounded B) :
    {z : ι → ℤ | (fun i => (z i : ℝ)) ∈ B}.Finite := by
  obtain ⟨I, hI, hsub⟩ := BoxIntegral.le_hasIntegralVertices_of_isBounded (ι := ι) hB
  obtain ⟨l, u, hl, hu⟩ := hI
  refine (Set.Finite.pi (fun i => (Finset.finite_toSet (Finset.Icc (l i) (u i))))).subset ?_
  intro z hz
  rw [Set.mem_pi]
  intro i _
  rw [Finset.mem_coe, Finset.mem_Icc]
  have h1 : I.lower i < (z i : ℝ) := ((hsub hz) i).1
  have h2 : (z i : ℝ) ≤ I.upper i := ((hsub hz) i).2
  rw [hl i] at h1
  rw [hu i] at h2
  exact ⟨le_of_lt (Int.cast_lt.mp h1), Int.cast_le.mp h2⟩

omit [Fintype ι] in
private lemma div_mem_smul_iff {m : ℝ} (hm : m ≠ 0) {s : Set (ι → ℝ)} {y : ι → ℝ} :
    (fun i => y i / m) ∈ s ↔ y ∈ m • s := by
  rw [Set.mem_smul_set_iff_inv_smul_mem₀ hm]
  have h : (fun i => y i / m) = m⁻¹ • y := by
    ext i
    simp only [Pi.smul_apply, smul_eq_mul]
    field_simp
  rw [h]

private lemma finite_of_shift_count {s : Set (ι → ℝ)} (hs : Bornology.IsBounded s) (u : ι → ℝ)
    {m : ℝ} (hm : m ≠ 0) :
    {z : ι → ℤ | (fun i => ((z i : ℝ) + u i) / m) ∈ s}.Finite := by
  have hbdd : Bornology.IsBounded {x : ι → ℝ | x + u ∈ m • s} := by
    obtain ⟨R, hR, hsub⟩ := (Bornology.IsBounded.smul₀ hs m).subset_ball_lt 0 0
    refine (Metric.isBounded_ball (x := (0 : ι → ℝ)) (r := R + ‖u‖)).subset ?_
    intro x hx
    have hb : ‖x + u‖ < R := by
      have h1 := hsub hx
      rw [Metric.mem_ball, dist_zero_right] at h1
      exact h1
    rw [Metric.mem_ball, dist_zero_right]
    calc ‖x‖ = ‖(x + u) - u‖ := by rw [add_sub_cancel_right]
      _ ≤ ‖x + u‖ + ‖u‖ := norm_sub_le _ _
      _ < R + ‖u‖ := by linarith
  have hfin : {z : ι → ℤ | (fun i => (z i : ℝ)) ∈ {x : ι → ℝ | x + u ∈ m • s}}.Finite :=
    finite_latticePoints_of_isBounded hbdd
  have hset : {z : ι → ℤ | (fun i => ((z i : ℝ) + u i) / m) ∈ s}
      = {z : ι → ℤ | (fun i => (z i : ℝ)) ∈ {x : ι → ℝ | x + u ∈ m • s}} := by
    ext z
    simp only [Set.mem_ofPred_eq]
    rw [div_mem_smul_iff hm]
    exact Iff.rfl
  rw [hset]
  exact hfin

/-- The shifted lattice-point count. -/
abbrev shiftCount (s : Set (ι → ℝ)) (u : ι → ℝ) (m : ℝ) : ℕ :=
  ({z : ι → ℤ | (fun i => ((z i : ℝ) + u i) / m) ∈ s} : Set (ι → ℤ)).ncard

/-- The periodic lattice-point count at scale `T`. -/
abbrev perCount (s : Set (ι → ℝ)) (P : (ι → ℤ) → Prop) (T : ℝ) : ℕ :=
  ({b : ι → ℤ | (fun i => (b i : ℝ) / T) ∈ s ∧ P b} : Set (ι → ℤ)).ncard

private lemma div_div_eq (a b q T : ℝ) (hq : q ≠ 0) (hT : T ≠ 0) :
    (a + b / q) / (T / q) = (a * q + b) / T := by
  rw [div_eq_div_iff (div_ne_zero hT hq) hT]
  field_simp

private lemma ncard_periodic_decomp {s : Set (ι → ℝ)} (hs : Bornology.IsBounded s)
    [DecidableEq ι] (Q : ℕ) (hQ : 1 ≤ Q) (P : (ι → ℤ) → Prop) [DecidablePred P]
    (hP : ∀ a b, P a ↔ P (a + (Q : ℤ) • b)) {T : ℝ} (hT : T ≠ 0) :
    (perCount s P T : ℝ)
      = ∑ c : ι → Fin Q, (if P (fun i => ((c i : ℕ) : ℤ)) then
          (shiftCount s (fun i => ((c i : ℕ) : ℝ) / Q) (T / Q) : ℝ)
        else 0) := by
  classical
  haveI : NeZero Q := ⟨by omega⟩
  have hQ0 : ((Q : ℝ)) ≠ 0 := by positivity
  have hTm : T / (Q:ℝ) ≠ 0 := div_ne_zero hT hQ0
  set e : (ι → ℤ) ≃ (ι → ℤ) × (ι → Fin Q) :=
    { toFun := fun b => (fun i => (Int.divModEquiv Q (b i)).1, fun i => (Int.divModEquiv Q (b i)).2)
      invFun := fun p => fun i => (Int.divModEquiv Q).symm (p.1 i, p.2 i)
      left_inv := fun b => by
        funext i
        exact (Int.divModEquiv Q).symm_apply_apply (b i)
      right_inv := fun p => by
        have h : ∀ i, (Int.divModEquiv Q) ((Int.divModEquiv Q).symm (p.1 i, p.2 i))
            = (p.1 i, p.2 i) := fun i => (Int.divModEquiv Q).apply_symm_apply (p.1 i, p.2 i)
        refine Prod.ext ?_ ?_ <;> funext i
        · exact congrArg Prod.fst (h i)
        · exact congrArg Prod.snd (h i) } with he
  set φ : (ι → ℤ) → Prop := fun b => (fun i => (b i : ℝ) / T) ∈ s ∧ P b with hφ
  change ({b : ι → ℤ | φ b}.ncard : ℝ) = _
  have hpred : ∀ (z : ι → ℤ) (c : ι → Fin Q), φ (e.symm (z, c)) ↔
      P (fun i => ((c i : ℕ) : ℤ)) ∧
        (fun i => ((z i : ℝ) + ((c i : ℕ) : ℝ) / (Q:ℝ)) / (T / (Q:ℝ))) ∈ s := by
    intro z c
    have hs1i : ∀ i, e.symm (z, c) i = z i * (Q:ℤ) + ((c i : ℕ) : ℤ) :=
      fun i => Int.divModEquiv_symm_apply Q (z i, c i)
    have hfun2 : e.symm (z, c) = fun i => z i * (Q:ℤ) + ((c i : ℕ) : ℤ) := funext hs1i
    have hfun1 : (fun i => (e.symm (z, c) i : ℝ) / T)
        = (fun i => ((z i : ℝ) + ((c i : ℕ) : ℝ) / (Q:ℝ)) / (T / (Q:ℝ))) := by
      funext i
      rw [hs1i i]
      push_cast
      exact (div_div_eq (z i) ((c i : ℕ) : ℝ) (Q:ℝ) T hQ0 hT).symm
    have hPz : P (fun i => z i * (Q:ℤ) + ((c i : ℕ) : ℤ)) ↔ P (fun i => ((c i : ℕ) : ℤ)) := by
      have h := hP (fun i => ((c i : ℕ) : ℤ)) z
      have hf : (fun i => ((c i : ℕ) : ℤ)) + (Q : ℤ) • z
          = fun i => z i * (Q:ℤ) + ((c i : ℕ) : ℤ) := by
        funext i
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        ring
      rw [hf] at h
      exact h.symm
    simp only [hφ]
    rw [hfun1, hfun2, hPz, and_comm]
  have hstep1 : ({b : ι → ℤ | φ b}.ncard : ℝ)
      = ({p : (ι → ℤ) × (ι → Fin Q) | φ (e.symm p)}.ncard : ℝ) := by
    congr 1
    refine Set.ncard_congr (fun b _ => e b) ?_ ?_ ?_
    · intro b hb
      simpa [Equiv.symm_apply_apply] using hb
    · intro b b' _ _ h
      exact e.injective h
    · intro p hp
      exact ⟨e.symm p, by simpa [Equiv.apply_symm_apply] using hp, e.apply_symm_apply p⟩
  have hfib : ∀ c : ι → Fin Q, {z : ι → ℤ | φ (e.symm (z, c))}.Finite := by
    intro c
    have hfin := finite_of_shift_count hs (fun i => ((c i : ℕ) : ℝ) / (Q:ℝ)) hTm
    refine hfin.subset ?_
    intro z hz
    exact (hpred z c).mp hz |>.2
  have hstep2 : ({p : (ι → ℤ) × (ι → Fin Q) | φ (e.symm p)}.ncard : ℝ)
      = ∑ c : ι → Fin Q, ({z : ι → ℤ | φ (e.symm (z, c))}.ncard : ℝ) := by
    letI : ∀ c : ι → Fin Q, Fintype {z : ι → ℤ // φ (e.symm (z, c))} := fun c => (hfib c).fintype
    have hnat : Nat.card {p : (ι → ℤ) × (ι → Fin Q) // φ (e.symm p)}
        = ∑ c : ι → Fin Q, Nat.card {z : ι → ℤ // φ (e.symm (z, c))} := by
      have e2 : {p : (ι → ℤ) × (ι → Fin Q) // φ (e.symm p)} ≃
          Σ c : ι → Fin Q, {z : ι → ℤ // φ (e.symm (z, c))} :=
        { toFun := fun p => ⟨p.1.2, ⟨p.1.1, p.2⟩⟩
          invFun := fun x => ⟨(x.2.1, x.1), x.2.2⟩
          left_inv := fun p => rfl
          right_inv := fun x => rfl }
      rw [Nat.card_congr e2, Nat.card_eq_fintype_card, Fintype.card_sigma]
      simp only [Nat.card_eq_fintype_card]
    have h1 : ({p : (ι → ℤ) × (ι → Fin Q) | φ (e.symm p)}.ncard : ℝ)
        = (Nat.card {p : (ι → ℤ) × (ι → Fin Q) // φ (e.symm p)} : ℝ) :=
      congrArg (fun n : ℕ => (n : ℝ)) (Nat.card_coe_set_eq _).symm
    have h2 : (∑ c : ι → Fin Q, (Nat.card {z : ι → ℤ // φ (e.symm (z, c))} : ℝ))
        = ∑ c : ι → Fin Q, ({z : ι → ℤ | φ (e.symm (z, c))}.ncard : ℝ) :=
      Finset.sum_congr rfl fun c _ =>
        congrArg (fun n : ℕ => (n : ℝ)) (Nat.card_coe_set_eq _).symm
    rw [h1, hnat]
    push_cast
    exact h2
  have hstep3 : ∀ c : ι → Fin Q, ({z : ι → ℤ | φ (e.symm (z, c))}.ncard : ℝ)
      = (if P (fun i => ((c i : ℕ) : ℤ)) then
          (shiftCount s (fun i => ((c i : ℕ) : ℝ) / Q) (T / Q) : ℝ)
        else 0) := by
    intro c
    by_cases hc : P (fun i => ((c i : ℕ) : ℤ))
    · rw [if_pos hc]
      have hset : {z : ι → ℤ | φ (e.symm (z, c))}
          = {z : ι → ℤ | (fun i => ((z i : ℝ) + ((c i : ℕ) : ℝ) / (Q:ℝ)) / (T / (Q:ℝ))) ∈ s} := by
        ext z
        rw [Set.mem_ofPred_eq, hpred z c]
        simp [hc]
      rw [hset]
    · rw [if_neg hc]
      have hset : {z : ι → ℤ | φ (e.symm (z, c))} = ∅ := by
        ext z
        rw [Set.mem_ofPred_eq, hpred z c]
        simp [hc]
      rw [hset, Set.ncard_empty]
      norm_num
  rw [hstep1, hstep2]
  exact Finset.sum_congr rfl fun c _ => hstep3 c

private lemma key_alg (A T U : ℝ) (hU : U ≠ 0) (hT : T ≠ 0) (K : ℕ) :
    A / U ^ K * (U / T) ^ K = A / T ^ K := by
  rw [div_pow]
  field_simp

/-- Periodic lattice-point count for a star-shaped set, over a real parameter `T → ∞`.
This is the `Q`-periodic refinement of Mathlib's `tendsto_card_div_pow_atTop_volume'`.

Route. (1) For each residue class `c : ι → Fin Q`, the map `z ↦ Q * z + c` is a bijection from
`ι → ℤ` onto the coset of `b` with `b ≡ c (mod Q)`, and
`(Q * z + c)/(Q * m) = (z + c/Q)/m`, so `shifted_card_div_pow_tendsto` (with `v = c/Q ∈ [0,1]^ι`)
gives the limit `(volume s)` for the count of each class, as `m → ∞`, divided by `m^card ι`.
Summing over the classes (use `hP` to replace `P b` by `P c` on the class) gives the limit
`Nat.card {c // P c} / Q^card ι * volume s` for `T = Q * m`.
(2) Extend from `T = Q * m` to arbitrary `T ∈ ℕ`: `#{b | b/T ∈ s ∧ P b}` is nondecreasing in `T`
by `hstar` (`b/T ∈ s → (T/T') • (b/T) = b/T' ∈ s` when `T ≤ T'`), so `⌊T/Q⌋ * Q` and `⌈T/Q⌉ * Q`
sandwich `T` and `(⌊T/Q⌋ * Q)/T → 1`.
(3) Extend from `T ∈ ℕ` to `T : ℝ` the same way, with `⌊T⌋₊` and `⌈T⌉₊`. -/
theorem periodic_count_real {ι : Type*} [Fintype ι] {s : Set (ι → ℝ)}
    (hs₁ : Bornology.IsBounded s) (hs₂ : MeasurableSet s)
    (hs₃ : MeasureTheory.volume (frontier s) = 0)
    (hstar : ∀ ⦃x y : ℝ⦄, 0 < x → x ≤ y → ∀ z : ι → ℝ, z ∈ s → (x / y) • z ∈ s)
    (Q : ℕ) (hQ : 1 ≤ Q) (P : (ι → ℤ) → Prop) (hP : ∀ a b, P a ↔ P (a + (Q : ℤ) • b)) :
    Filter.Tendsto (fun T : ℝ =>
        (({b : ι → ℤ | (fun i => (b i : ℝ) / T) ∈ s ∧ P b} : Set (ι → ℤ)).ncard : ℝ) /
          T ^ Fintype.card ι)
      Filter.atTop (nhds ((Nat.card {c : ι → Fin Q // P (fun i => ((c i : ℕ) : ℤ))} : ℝ) /
        (Q : ℝ) ^ Fintype.card ι * (MeasureTheory.volume s).toReal)) := by
  classical
  set L : ℝ := (volume s).toReal with hL
  set Kl : ℝ := (Nat.card {c : ι → Fin Q // P (fun i => ((c i : ℕ) : ℤ))} : ℝ) with hKl
  set R : ℝ := Kl / (Q : ℝ) ^ Fintype.card ι * L with hR
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hmono : ∀ {T T' : ℝ}, 0 < T → T ≤ T' → (perCount s P T : ℝ) ≤ (perCount s P T' : ℝ) := by
    intro T T' hT hTT'
    have hT' : 0 < T' := lt_of_lt_of_le hT hTT'
    have hsub : {b : ι → ℤ | (fun i => (b i : ℝ) / T) ∈ s ∧ P b}
        ⊆ {b : ι → ℤ | (fun i => (b i : ℝ) / T') ∈ s ∧ P b} := by
      intro b hb
      refine ⟨?_, hb.2⟩
      have h := hstar (x := T) (y := T') hT hTT' (fun i => (b i : ℝ) / T) hb.1
      rwa [show (T / T') • (fun i => (b i : ℝ) / T) = fun i => (b i : ℝ) / T' from ?_] at h
      ext i
      simp only [Pi.smul_apply, smul_eq_mul]
      field_simp
    have hfin : ({b : ι → ℤ | (fun i => (b i : ℝ) / T') ∈ s ∧ P b} : Set (ι → ℤ)).Finite :=
      (finite_of_shift_count hs₁ (0 : ι → ℝ) hT'.ne').subset (fun b hb => by simpa using hb.1)
    show (({b : ι → ℤ | (fun i => (b i : ℝ) / T) ∈ s ∧ P b} : Set (ι → ℤ)).ncard : ℝ)
       ≤ (({b : ι → ℤ | (fun i => (b i : ℝ) / T') ∈ s ∧ P b} : Set (ι → ℤ)).ncard : ℝ)
    exact_mod_cast Set.ncard_le_ncard hsub hfin
  have hterm : ∀ c : ι → Fin Q, Tendsto (fun m : ℕ =>
        (if P (fun i => ((c i : ℕ) : ℤ)) then
          (shiftCount s (fun i => ((c i : ℕ) : ℝ) / (Q : ℝ)) (m : ℝ) : ℝ)
            / ((Q : ℝ) * (m : ℝ)) ^ Fintype.card ι else 0))
      atTop (nhds (if P (fun i => ((c i : ℕ) : ℤ)) then L / (Q : ℝ) ^ Fintype.card ι else 0)) := by
    intro c
    by_cases hc : P (fun i => ((c i : ℕ) : ℤ))
    · have hv : ∀ i, 0 ≤ ((c i : ℕ) : ℝ) / (Q : ℝ) ∧ ((c i : ℕ) : ℝ) / (Q : ℝ) ≤ 1 := by
        intro i
        refine ⟨by positivity, ?_⟩
        rw [div_le_one hQpos]
        exact_mod_cast le_of_lt (c i).isLt
      have h0 := shifted_card_div_pow_tendsto (s := s) hs₁ hs₂ hs₃
        (fun i => ((c i : ℕ) : ℝ) / (Q : ℝ)) hv
      have hfun : (fun m : ℕ => (if P (fun i => ((c i : ℕ) : ℤ)) then
            (shiftCount s (fun i => ((c i : ℕ) : ℝ) / (Q : ℝ)) (m : ℝ) : ℝ)
              / ((Q : ℝ) * (m : ℝ)) ^ Fintype.card ι else 0))
          = fun m : ℕ => (shiftCount s (fun i => ((c i : ℕ) : ℝ) / (Q : ℝ)) (m : ℝ) : ℝ)
              / ((Q : ℝ) * (m : ℝ)) ^ Fintype.card ι := by
        funext m
        rw [if_pos hc]
      rw [hfun, if_pos hc, hL]
      refine (h0.div_const ((Q : ℝ) ^ Fintype.card ι)).congr' ?_
      filter_upwards with m
      have hden : ((Q : ℝ) * (m : ℝ)) ^ Fintype.card ι
          = (m : ℝ) ^ Fintype.card ι * (Q : ℝ) ^ Fintype.card ι := by
        rw [mul_pow, mul_comm]
      rw [hden, div_div]
    · have hfun : (fun m : ℕ => (if P (fun i => ((c i : ℕ) : ℤ)) then
            (shiftCount s (fun i => ((c i : ℕ) : ℝ) / (Q : ℝ)) (m : ℝ) : ℝ)
              / ((Q : ℝ) * (m : ℝ)) ^ Fintype.card ι else 0)) = fun _ : ℕ => 0 := by
        funext m
        rw [if_neg hc]
      rw [hfun, if_neg hc]
      exact tendsto_const_nhds
  have hG : Tendsto (fun m : ℕ =>
      (perCount s P ((Q : ℝ) * (m : ℝ)) : ℝ) / ((Q : ℝ) * (m : ℝ)) ^ Fintype.card ι)
      atTop (nhds R) := by
    have hsum := tendsto_finsetSum (Finset.univ : Finset (ι → Fin Q)) (fun c _ => hterm c)
    have hlim : (∑ c ∈ (Finset.univ : Finset (ι → Fin Q)),
        (if P (fun i => ((c i : ℕ) : ℤ)) then L / (Q : ℝ) ^ Fintype.card ι else 0)) = R := by
      have hcard : (∑ c : ι → Fin Q, (if P (fun i => ((c i : ℕ) : ℤ)) then (1 : ℝ) else 0))
          = Kl := by
        rw [hKl, Nat.card_eq_fintype_card, Fintype.card_subtype, Finset.card_filter]
        push_cast
        rfl
      have hsplit : (∑ c : ι → Fin Q,
            (if P (fun i => ((c i : ℕ) : ℤ)) then L / (Q : ℝ) ^ Fintype.card ι else 0))
          = (∑ c : ι → Fin Q, (if P (fun i => ((c i : ℕ) : ℤ)) then (1 : ℝ) else 0))
              * (L / (Q : ℝ) ^ Fintype.card ι) := by
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun c _ => by split_ifs <;> ring
      rw [hR, hsplit, hcard]
      ring
    rw [hlim] at hsum
    refine hsum.congr' ?_
    filter_upwards [eventually_ne_atTop (0 : ℕ)] with m hm
    have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm
    have hT : ((Q : ℝ) * (m : ℝ)) ≠ 0 := by positivity
    have hdecomp := ncard_periodic_decomp (s := s) hs₁ Q hQ P hP (T := (Q : ℝ) * (m : ℝ)) hT
    have hQm : ((Q : ℝ) * (m : ℝ)) / (Q : ℝ) = (m : ℝ) := by
      rw [mul_div_assoc]
      exact mul_div_cancel₀ (m : ℝ) hQpos.ne'
    rw [hQm] at hdecomp
    rw [hdecomp, Finset.sum_div]
    exact Finset.sum_congr rfl fun c _ => by split_ifs <;> ring
  have hfloor : Tendsto (fun T : ℝ => ⌊T / (Q : ℝ)⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp (tendsto_id.atTop_div_const hQpos)
  have hceil : Tendsto (fun T : ℝ => ⌈T / (Q : ℝ)⌉₊) atTop atTop :=
    tendsto_nat_ceil_atTop.comp (tendsto_id.atTop_div_const hQpos)
  have hrlow : Tendsto (fun T : ℝ => ((Q : ℝ) * (⌊T / (Q : ℝ)⌋₊ : ℝ)) / T) atTop (nhds 1) := by
    have h := tendsto_nat_floor_div_atTop.comp (tendsto_id.atTop_div_const hQpos)
    refine h.congr' ?_
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with T hT
    simp only [Function.comp_apply, id_eq]
    rw [div_div_eq_mul_div]
    ring
  have hrup : Tendsto (fun T : ℝ => ((Q : ℝ) * (⌈T / (Q : ℝ)⌉₊ : ℝ)) / T) atTop (nhds 1) := by
    have h := tendsto_nat_ceil_div_atTop.comp (tendsto_id.atTop_div_const hQpos)
    refine h.congr' ?_
    filter_upwards [eventually_ne_atTop (0 : ℝ)] with T hT
    simp only [Function.comp_apply, id_eq]
    rw [div_div_eq_mul_div]
    ring
  have hGlow : Tendsto (fun T : ℝ =>
      (perCount s P ((Q : ℝ) * (⌊T / (Q : ℝ)⌋₊ : ℝ)) : ℝ)
        / ((Q : ℝ) * (⌊T / (Q : ℝ)⌋₊ : ℝ)) ^ Fintype.card ι
      * (((Q : ℝ) * (⌊T / (Q : ℝ)⌋₊ : ℝ)) / T) ^ Fintype.card ι) atTop (nhds R) := by
    have h := (hG.comp hfloor).mul (hrlow.pow (Fintype.card ι))
    simpa using h
  have hGup : Tendsto (fun T : ℝ =>
      (perCount s P ((Q : ℝ) * (⌈T / (Q : ℝ)⌉₊ : ℝ)) : ℝ)
        / ((Q : ℝ) * (⌈T / (Q : ℝ)⌉₊ : ℝ)) ^ Fintype.card ι
      * (((Q : ℝ) * (⌈T / (Q : ℝ)⌉₊ : ℝ)) / T) ^ Fintype.card ι) atTop (nhds R) := by
    have h := (hG.comp hceil).mul (hrup.pow (Fintype.card ι))
    simpa using h
  have hlow_le : ∀ᶠ T : ℝ in atTop,
      (perCount s P ((Q : ℝ) * (⌊T / (Q : ℝ)⌋₊ : ℝ)) : ℝ)
        / ((Q : ℝ) * (⌊T / (Q : ℝ)⌋₊ : ℝ)) ^ Fintype.card ι
      * (((Q : ℝ) * (⌊T / (Q : ℝ)⌋₊ : ℝ)) / T) ^ Fintype.card ι
      ≤ (perCount s P T : ℝ) / T ^ Fintype.card ι := by
    filter_upwards [eventually_ge_atTop (Q : ℝ)] with T hT
    have hTpos : 0 < T := lt_of_lt_of_le hQpos hT
    have hm1 : 1 ≤ ⌊T / (Q : ℝ)⌋₊ :=
      Nat.le_floor (by rw [le_div_iff₀ hQpos]; simpa using hT)
    have hQmpos : (0 : ℝ) < (Q : ℝ) * (⌊T / (Q : ℝ)⌋₊ : ℝ) := by
      have hm1' : (0 : ℝ) < (⌊T / (Q : ℝ)⌋₊ : ℝ) := by exact_mod_cast hm1
      positivity
    have hQmle : (Q : ℝ) * (⌊T / (Q : ℝ)⌋₊ : ℝ) ≤ T := by
      have h1 : (⌊T / (Q : ℝ)⌋₊ : ℝ) ≤ T / (Q : ℝ) := Nat.floor_le (by positivity)
      have h2 := mul_le_mul_of_nonneg_left h1 hQpos.le
      rwa [mul_div_cancel₀ T hQpos.ne'] at h2
    have hmon := hmono hQmpos hQmle
    rw [key_alg _ T _ hQmpos.ne' hTpos.ne']
    exact div_le_div_of_nonneg_right hmon (by positivity)
  have hup_le : ∀ᶠ T : ℝ in atTop,
      (perCount s P T : ℝ) / T ^ Fintype.card ι
      ≤ (perCount s P ((Q : ℝ) * (⌈T / (Q : ℝ)⌉₊ : ℝ)) : ℝ)
        / ((Q : ℝ) * (⌈T / (Q : ℝ)⌉₊ : ℝ)) ^ Fintype.card ι
      * (((Q : ℝ) * (⌈T / (Q : ℝ)⌉₊ : ℝ)) / T) ^ Fintype.card ι := by
    filter_upwards [eventually_ge_atTop (Q : ℝ)] with T hT
    have hTpos : 0 < T := lt_of_lt_of_le hQpos hT
    have hm1 : 1 ≤ ⌈T / (Q : ℝ)⌉₊ := by
      have h1 : (1 : ℝ) ≤ T / (Q : ℝ) := by rw [le_div_iff₀ hQpos, one_mul]; exact hT
      have h2 : (1 : ℝ) ≤ (⌈T / (Q : ℝ)⌉₊ : ℝ) := le_trans h1 (Nat.le_ceil _)
      exact_mod_cast h2
    have hQmpos : (0 : ℝ) < (Q : ℝ) * (⌈T / (Q : ℝ)⌉₊ : ℝ) := by
      have hm1' : (0 : ℝ) < (⌈T / (Q : ℝ)⌉₊ : ℝ) := by exact_mod_cast hm1
      positivity
    have hQmge : T ≤ (Q : ℝ) * (⌈T / (Q : ℝ)⌉₊ : ℝ) := by
      have h1 : T / (Q : ℝ) ≤ (⌈T / (Q : ℝ)⌉₊ : ℝ) := Nat.le_ceil _
      have h2 := mul_le_mul_of_nonneg_left h1 hQpos.le
      rwa [mul_div_cancel₀ T hQpos.ne'] at h2
    have hmon := hmono hTpos hQmge
    rw [key_alg _ T _ hQmpos.ne' hTpos.ne']
    exact div_le_div_of_nonneg_right hmon (by positivity)
  have hfinal : Tendsto (fun T : ℝ => (perCount s P T : ℝ) / T ^ Fintype.card ι) atTop (nhds R) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' hGlow hGup hlow_le hup_le
  simpa [perCount] using hfinal

end Work.HP.DNC
