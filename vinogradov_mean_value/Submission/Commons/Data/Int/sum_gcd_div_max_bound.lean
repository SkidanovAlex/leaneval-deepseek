import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.NumberTheory.Harmonic.Bounds
import Mathlib.Order.Interval.Finset.Box

open scoped BigOperators

set_option autoImplicit false

namespace Commons.Data.Int

-- value of one summand, as a function of the absolute values
noncomputable def val (a b : ℕ) : ℝ :=
  (Nat.gcd a b : ℝ) / (max a b : ℝ)

-- divisor-type upper bound on val |d| |g|, for pairs with |d|,|g| ≤ N
noncomputable def ub (N : ℕ) (a b : ℕ) : ℝ :=
  ∑ e ∈ Finset.Icc 1 N,
    if e ∣ a ∧ e ∣ b then (e : ℝ) / (max a b : ℝ) else 0

-- summand of the target sum
noncomputable def term (d g : ℤ) : ℝ :=
  (Int.gcd d.natAbs g.natAbs : ℝ) / (max d.natAbs g.natAbs : ℝ)

/-- the `if (d,g) = (0,0) then 0 else ...` in the target equals the plain value
(since `x / 0 = 0` in `ℝ`) -/
lemma term_if_eq (d g : ℤ) :
    (if (d, g) = (0, 0) then (0 : ℝ)
      else ((Int.gcd d.natAbs g.natAbs : ℝ) / (max d.natAbs g.natAbs : ℝ))) =
    term d g := by
  by_cases h : (d, g) = (0, 0)
  · have hd : d = 0 := congrArg Prod.fst h
    have hg : g = 0 := congrArg Prod.snd h
    subst d
    subst g
    simp [term]
  · simp [term, h]

/-- `Int.gcd d.natAbs g.natAbs` equals `Nat.gcd d.natAbs g.natAbs` -/
lemma int_gcd_natAbs (d g : ℤ) : Int.gcd d.natAbs g.natAbs = Nat.gcd d.natAbs g.natAbs := by
  rw [Int.gcd_def]
  rw [Int.natAbs_natCast]
  rw [Int.natAbs_natCast]

/-- termwise bound of the value by the divisor sum -/
lemma val_le_ub (N : ℕ) (a b : ℕ) (ha : a ≤ N) (hb : b ≤ N) :
    val a b ≤ ub N a b := by
  by_cases h00 : a = 0 ∧ b = 0
  · rcases h00 with ⟨rfl, rfl⟩
    simp [val, ub]
  · let f : ℕ → ℝ := fun e => if (e ∣ a ∧ e ∣ b) then (e : ℝ) else 0
    have hmaxnz : (0 : ℕ) < max a b := by
      rw [Nat.pos_iff_ne_zero]
      intro hm
      exact h00 ⟨le_antisymm (by simpa [hm] using Nat.le_max_left a b) (Nat.zero_le a),
        le_antisymm (by simpa [hm] using Nat.le_max_right a b) (Nat.zero_le b)⟩
    have hg1 : 1 ≤ Nat.gcd a b := by
      by_cases ha0 : a = 0
      · subst a
        have hb0 : b ≠ 0 := by
          intro hb0
          exact h00 ⟨rfl, hb0⟩
        rw [Nat.gcd_zero_left]
        omega
      · exact Nat.gcd_pos_of_pos_left b (Nat.pos_of_ne_zero ha0)
    have hgN : Nat.gcd a b ≤ N := by
      by_cases ha0 : a = 0
      · subst a
        rw [Nat.gcd_zero_left]
        exact hb
      · exact (Nat.le_of_dvd (Nat.pos_of_ne_zero ha0) (Nat.gcd_dvd_left a b)).trans ha
    have hgmem : Nat.gcd a b ∈ Finset.Icc 1 N := by
      rw [Finset.mem_Icc]
      exact ⟨hg1, hgN⟩
    have hcond : Nat.gcd a b ∣ a ∧ Nat.gcd a b ∣ b :=
      ⟨Nat.gcd_dvd_left a b, Nat.gcd_dvd_right a b⟩
    have hnonneg : ∀ e ∈ Finset.Icc 1 N, 0 ≤ f e := by
      intro e he
      by_cases c : e ∣ a ∧ e ∣ b <;> simp [f, c]
    have hsingle := Finset.single_le_sum hnonneg hgmem
    have hfgcd : f (Nat.gcd a b) = (Nat.gcd a b : ℝ) := by simp [f, hcond]
    have hsum : (Nat.gcd a b : ℝ) ≤ ∑ e ∈ Finset.Icc 1 N, f e := by
      rwa [hfgcd] at hsingle
    have hmaxℝ : 0 < (max a b : ℝ) := by exact_mod_cast hmaxnz
    calc
      val a b = (Nat.gcd a b : ℝ) / (max a b : ℝ) := rfl
      _ ≤ (∑ e ∈ Finset.Icc 1 N, f e) / (max a b : ℝ) :=
        div_le_div_of_nonneg_right hsum (le_of_lt hmaxℝ)
      _ = ub N a b := by
        unfold ub
        rw [div_eq_mul_inv, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro e he
        by_cases c : e ∣ a ∧ e ∣ b
        · simp [f, c]
          rw [div_eq_mul_inv]
        · simp [f, c]

/-- `fp` on pairs: reciprocal of the max of the two `natAbs`s -/
noncomputable def fp (x : ℤ × ℤ) : ℝ :=
  (1 : ℝ) / max (x.1.natAbs : ℝ) (x.2.natAbs : ℝ)

private lemma box_sum_fp (M : ℕ) :
    (∑ x ∈ Finset.Icc (-(M : ℤ × ℤ)) (M : ℤ × ℤ), fp x) = 8 * (M : ℝ) := by
  induction M with
  | zero => simp [fp]
  | succ M ih =>
      rw [← Finset.box_succ_union_prod]
      rw [Finset.sum_union (Finset.disjoint_box_succ_prod M)]
      rw [ih]
      have hconst : ∀ x ∈ Finset.box (M + 1), fp x = (1 : ℝ) / (M + 1 : ℝ) := by
        intro x hx
        have hm : max x.1.natAbs x.2.natAbs = M + 1 := Int.mem_box.mp hx
        have hm' : max (x.1.natAbs : ℝ) (x.2.natAbs : ℝ) = (M + 1 : ℝ) := by
          rw [← Nat.cast_max]
          exact_mod_cast hm
        rw [fp, hm']
      rw [Finset.sum_congr rfl hconst]
      rw [Finset.sum_const, nsmul_eq_mul]
      rw [Int.card_box (by omega : (M + 1) ≠ 0)]
      norm_num
      field_simp
      ring

/-- the sum of `1 / max |d| |g|` over the full grid of size M equals `8 * M` -/
lemma grid_inv_max_sum (M : ℕ) :
    (∑ d ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
      ∑ g ∈ Finset.Icc (-(M : ℤ)) (M : ℤ),
        (1 : ℝ) / max (d.natAbs : ℝ) (g.natAbs : ℝ)) = 8 * (M : ℝ) := by
  change (∑ d ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), ∑ g ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), fp (d, g))
      = 8 * (M : ℝ)
  rw [← Finset.sum_product (s := Finset.Icc (-(M : ℤ)) (M : ℤ))
      (t := Finset.Icc (-(M : ℤ)) (M : ℤ)) (f := fp)]
  have hIcc : (Finset.Icc (-(M : ℤ)) (M : ℤ)) ×ˢ (Finset.Icc (-(M : ℤ)) (M : ℤ)) =
      Finset.Icc (-(M : ℤ × ℤ)) (M : ℤ × ℤ) := by
    exact (Finset.Icc_prod_def (-(M : ℤ × ℤ)) (M : ℤ × ℤ)).symm
  rw [hIcc]
  exact box_sum_fp M

/-- harmonic bound: sum of reciprocals up to N is at most 1 + log (N + 1) -/
lemma sum_inv_le_one_add_log (N : ℕ) (hN : 1 ≤ N) :
    (∑ e ∈ Finset.Icc 1 N, (1 : ℝ) / (e : ℝ)) ≤ 1 + Real.log ((N : ℝ) + 1) := by
  calc
    (∑ e ∈ Finset.Icc 1 N, (1 : ℝ) / (e : ℝ)) = (harmonic N : ℝ) := by
      rw [harmonic_eq_sum_Icc]
      rw [Rat.cast_sum]
      apply Finset.sum_congr rfl
      intro e he
      simp [Rat.cast_inv]
    _ ≤ 1 + Real.log (N : ℝ) := harmonic_le_one_add_log N
    _ ≤ 1 + Real.log ((N : ℝ) + 1) := by
      have hmono : Real.log (N : ℝ) ≤ Real.log ((N : ℝ) + 1) :=
        Real.log_le_log (by positivity : 0 < (N : ℝ)) (by linarith)
      linarith


/-- membership in a symmetric integer interval, in terms of `natAbs` -/
private lemma mem_Gm_iff (n : ℕ) (x : ℤ) : x ∈ Finset.Icc (-(n : ℤ)) (n : ℤ) ↔ x.natAbs ≤ n := by
  rw [Finset.mem_Icc]
  rw [← abs_le]
  rw [Int.abs_eq_natAbs]
  constructor
  · intro h
    exact_mod_cast h
  · intro h
    exact_mod_cast h

/-- change of variables `d = e * d'` in a sum over a symmetric interval:
an `e | natAbs d`-filtered sum over `[−N,N]` equals the unweighted sum over
`[−N/e, N/e]` of the values at `e · d'`. -/
private lemma sum_multiples_eq (N e M : ℕ) (hM : N / e = M) (he : 1 ≤ e) (F : ℤ → ℝ) :
    (∑ d ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), if e ∣ d.natAbs then F d else 0) =
      ∑ d' ∈ Finset.Icc (-(M : ℤ)) (M : ℤ), F ((e : ℤ) * d') := by
  classical
  let s : Finset ℤ := (Finset.Icc (-(N : ℤ)) (N : ℤ)).filter (fun d => e ∣ d.natAbs)
  let u : Finset ℤ := Finset.Icc (-(M : ℤ)) (M : ℤ)
  have he0 : 0 < e := by omega
  have hne : (e : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt he0)
  calc
    (∑ d ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), if e ∣ d.natAbs then F d else 0) = ∑ d ∈ s, F d := by
      rw [Finset.sum_filter]
    _ = ∑ d' ∈ u, F ((e : ℤ) * d') := by
      refine Finset.sum_bij' (s := s) (t := u)
        (i := fun a _ => a / (e : ℤ)) (j := fun b _ => (e : ℤ) * b) ?hi ?hj ?linv ?rinv ?hfun
      · intro a ha
        have haG : a ∈ Finset.Icc (-(N : ℤ)) (N : ℤ) := by
          simpa [s] using (Finset.mem_filter.mp ha).1
        have hae : e ∣ a.natAbs := by
          simpa [s] using (Finset.mem_filter.mp ha).2
        have haZ : (e : ℤ) ∣ a := Int.natCast_dvd.mpr hae
        have hdiv : a = (e : ℤ) * (a / (e : ℤ)) := by
          rw [mul_comm]
          exact (Int.ediv_mul_cancel haZ).symm
        have hna : ((e : ℤ) * (a / (e : ℤ))).natAbs = a.natAbs :=
          congrArg Int.natAbs hdiv.symm
        have haabs : ((a / (e : ℤ)).natAbs) * e = a.natAbs := by
          rw [Int.natAbs_mul, Int.natAbs_natCast] at hna
          rwa [mul_comm] at hna
        have han : a.natAbs ≤ N := (mem_Gm_iff N a).mp haG
        have hle : ((a / (e : ℤ)).natAbs) ≤ N / e := by
          rw [Nat.le_div_iff_mul_le he0]
          exact haabs.trans_le han
        rw [hM] at hle
        change (a / (e : ℤ)) ∈ Finset.Icc (-(M : ℤ)) (M : ℤ)
        exact (mem_Gm_iff M (a / (e : ℤ))).mpr hle
      · intro b hb
        have hbG : b.natAbs ≤ M := (mem_Gm_iff M b).mp hb
        have heq : ((e : ℤ) * b).natAbs = e * b.natAbs := by
          rw [Int.natAbs_mul]
          rw [Int.natAbs_natCast]
        have hbG' : b.natAbs ≤ N / e := by simpa [hM] using hbG
        have h1 : e * b.natAbs ≤ e * (N / e) := Nat.mul_le_mul_left e hbG'
        have hleN : ((e : ℤ) * b).natAbs ≤ N := by
          rw [heq]
          exact h1.trans (Nat.mul_div_le N e)
        have hdvde : e ∣ ((e : ℤ) * b).natAbs := by
          rw [heq]
          exact Nat.dvd_mul_right e b.natAbs
        change (e : ℤ) * b ∈ (Finset.Icc (-(N : ℤ)) (N : ℤ)).filter (fun d => e ∣ d.natAbs)
        exact Finset.mem_filter.mpr ⟨(mem_Gm_iff N ((e : ℤ) * b)).mpr hleN, hdvde⟩
      · intro a ha
        have hae : e ∣ a.natAbs := by
          simpa [s] using (Finset.mem_filter.mp ha).2
        have haZ : (e : ℤ) ∣ a := Int.natCast_dvd.mpr hae
        rw [mul_comm]
        exact Int.ediv_mul_cancel haZ
      · intro b hb
        rw [mul_comm]
        exact Int.mul_ediv_cancel b hne
      · intro a ha
        have hae : e ∣ a.natAbs := by
          simpa [s] using (Finset.mem_filter.mp ha).2
        have haZ : (e : ℤ) ∣ a := Int.natCast_dvd.mpr hae
        congr 1
        rw [mul_comm]
        exact (Int.ediv_mul_cancel haZ).symm

/-- grid sum of `ub ∘ |·|` rewrites as sum over e of inner sums -/
lemma grid_ub_sum (N : ℕ) :
    (∑ d ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      ∑ g ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ub N d.natAbs g.natAbs) =
    ∑ e ∈ Finset.Icc 1 N,
      (∑ d ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        ∑ g ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
          if e ∣ d.natAbs ∧ e ∣ g.natAbs then (e : ℝ) / (max d.natAbs g.natAbs : ℝ) else 0) := by
  unfold ub
  let G := Finset.Icc (-(N : ℤ)) (N : ℤ)
  let S := Finset.Icc 1 N
  let w : ℕ → ℤ → ℤ → ℝ := fun e d g =>
    if e ∣ d.natAbs ∧ e ∣ g.natAbs then (e : ℝ) / (max d.natAbs g.natAbs : ℝ) else 0
  change (∑ d ∈ G, ∑ g ∈ G, ∑ e ∈ S, w e d g) = ∑ e ∈ S, ∑ d ∈ G, ∑ g ∈ G, w e d g
  calc
    (∑ d ∈ G, ∑ g ∈ G, ∑ e ∈ S, w e d g)
        = (∑ d ∈ G, ∑ e ∈ S, ∑ g ∈ G, w e d g) := by
            apply Finset.sum_congr rfl
            intro d hd
            exact Finset.sum_comm (s := G) (t := S) (f := fun (g : ℤ) (e : ℕ) => w e d g)
    _ = ∑ e ∈ S, ∑ d ∈ G, ∑ g ∈ G, w e d g := by
            exact Finset.sum_comm (s := G) (t := S) (f := fun (d : ℤ) (e : ℕ) => ∑ g ∈ G, w e d g)

/-- inner sum over multiples of e: change variables d = e d', g = e g' -/
lemma inner_eq (N e : ℕ) (he : 1 ≤ e) :
    (∑ d ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      ∑ g ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        if e ∣ d.natAbs ∧ e ∣ g.natAbs then (e : ℝ) / (max d.natAbs g.natAbs : ℝ) else 0) =
    (∑ d ∈ Finset.Icc (-((N / e : ℕ) : ℤ)) ((N / e : ℕ) : ℤ),
      ∑ g ∈ Finset.Icc (-((N / e : ℕ) : ℤ)) ((N / e : ℕ) : ℤ),
        (1 : ℝ) / (max d.natAbs g.natAbs : ℝ)) := by
  have hne : (e : ℤ) ≠ 0 := by exact_mod_cast (ne_of_gt (by omega : 0 < e))
  have hsplit : ∀ d : ℤ, (∑ g ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
      if e ∣ d.natAbs ∧ e ∣ g.natAbs then (e : ℝ) / (max d.natAbs g.natAbs : ℝ) else 0)
      = (if e ∣ d.natAbs then
          ∑ g ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
            (if e ∣ g.natAbs then (e : ℝ) / (max d.natAbs g.natAbs : ℝ) else 0)
        else 0) := by
    intro d
    by_cases hd : e ∣ d.natAbs
    · simp [hd]
    · simp [hd]
  calc
    (∑ d ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), ∑ g ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
        if e ∣ d.natAbs ∧ e ∣ g.natAbs then (e : ℝ) / (max d.natAbs g.natAbs : ℝ) else 0)
        = (∑ d ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
            if e ∣ d.natAbs then
              ∑ g ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
                (if e ∣ g.natAbs then (e : ℝ) / (max d.natAbs g.natAbs : ℝ) else 0)
            else 0) := by
            apply Finset.sum_congr rfl
            intro d hd
            exact hsplit d
    _ = (∑ d ∈ Finset.Icc (-((N / e : ℕ) : ℤ)) ((N / e : ℕ) : ℤ),
          ∑ g ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
            (if e ∣ g.natAbs then (e : ℝ) / (max ((e : ℤ) * d).natAbs g.natAbs : ℝ) else 0)) := by
            rw [sum_multiples_eq N e (N / e) rfl he]
    _ = (∑ d ∈ Finset.Icc (-((N / e : ℕ) : ℤ)) ((N / e : ℕ) : ℤ),
          ∑ g ∈ Finset.Icc (-((N / e : ℕ) : ℤ)) ((N / e : ℕ) : ℤ),
          (e : ℝ) / (max ((e : ℤ) * d).natAbs ((e : ℤ) * g).natAbs : ℝ)) := by
            apply Finset.sum_congr rfl
            intro d hd
            rw [sum_multiples_eq N e (N / e) rfl he]
    _ = (∑ d ∈ Finset.Icc (-((N / e : ℕ) : ℤ)) ((N / e : ℕ) : ℤ),
          ∑ g ∈ Finset.Icc (-((N / e : ℕ) : ℤ)) ((N / e : ℕ) : ℤ),
          (1 : ℝ) / (max d.natAbs g.natAbs : ℝ)) := by
            apply Finset.sum_congr rfl
            intro d hd
            apply Finset.sum_congr rfl
            intro g hg
            have hnd : ((e : ℤ) * d).natAbs = e * d.natAbs := by
              rw [Int.natAbs_mul, Int.natAbs_natCast]
            have hng : ((e : ℤ) * g).natAbs = e * g.natAbs := by
              rw [Int.natAbs_mul, Int.natAbs_natCast]
            rw [hnd, hng]
            have hden : max ((e * d.natAbs : ℕ) : ℝ) ((e * g.natAbs : ℕ) : ℝ) =
                (e : ℝ) * max (d.natAbs : ℝ) (g.natAbs : ℝ) := by
              calc
                max ((e * d.natAbs : ℕ) : ℝ) ((e * g.natAbs : ℕ) : ℝ)
                    = (((max (e * d.natAbs) (e * g.natAbs) : ℕ)) : ℝ) := by rw [Nat.cast_max]
                _ = (((e * max d.natAbs g.natAbs) : ℕ) : ℝ) := by
                      congr 1
                      exact (max_mul_mul_left (e : ℕ) d.natAbs g.natAbs)
                _ = (e : ℝ) * ((max d.natAbs g.natAbs : ℕ) : ℝ) := by norm_num
                _ = (e : ℝ) * max (d.natAbs : ℝ) (g.natAbs : ℝ) := by rw [Nat.cast_max]
            rw [hden]
            have hne' : (e : ℝ) ≠ 0 := by
              exact_mod_cast (ne_of_gt (by omega : 0 < e))
            field_simp [hne']



theorem sum_gcd_div_max_bound (N : ℕ) (hN : 1 ≤ N) :
    ((Finset.Icc (-(N : ℤ)) (N : ℤ)).sum (fun d =>
      (Finset.Icc (-(N : ℤ)) (N : ℤ)).sum (fun g =>
        if (d, g) = (0, 0) then (0 : ℝ)
        else ((Int.gcd d.natAbs g.natAbs : ℝ) / (max d.natAbs g.natAbs : ℝ)))))
      ≤ 1000 * (N : ℝ) * (1 + Real.log ((N : ℝ) + 1)) := by
  classical
  let G : Finset ℤ := Finset.Icc (-(N : ℤ)) (N : ℤ)
  have hmemN : ∀ x : ℤ, x ∈ G → x.natAbs ≤ N := by
    intro x hx
    exact (mem_Gm_iff N x).mp hx
  have hlog0 : 0 ≤ Real.log ((N : ℝ) + 1) := by
    rw [show ((N : ℝ) + 1) = ((N + 1 : ℕ) : ℝ) by norm_num]
    exact Real.log_natCast_nonneg (N + 1)
  have hN0 : 0 ≤ (N : ℝ) := by positivity
  -- main estimate on the reduced (sum over e) expression
  have hmain : (∑ e ∈ Finset.Icc 1 N, 8 * ((N / e : ℕ) : ℝ)) ≤
      8 * ((N : ℝ) * (1 + Real.log ((N : ℝ) + 1))) := by
    calc
      (∑ e ∈ Finset.Icc 1 N, 8 * ((N / e : ℕ) : ℝ))
          = 8 * (∑ e ∈ Finset.Icc 1 N, ((N / e : ℕ) : ℝ)) := by
              rw [Finset.mul_sum]
      _ ≤ 8 * (∑ e ∈ Finset.Icc 1 N, (N : ℝ) / (e : ℝ)) := by
              have h1 : (∑ e ∈ Finset.Icc 1 N, ((N / e : ℕ) : ℝ)) ≤
                  ∑ e ∈ Finset.Icc 1 N, (N : ℝ) / (e : ℝ) :=
                Finset.sum_le_sum (fun e he => Nat.cast_div_le)
              exact mul_le_mul_of_nonneg_left h1 (by norm_num)
      _ = 8 * ((N : ℝ) * (∑ e ∈ Finset.Icc 1 N, (1 : ℝ) / (e : ℝ))) := by
              congr 1
              calc
                (∑ e ∈ Finset.Icc 1 N, (N : ℝ) / (e : ℝ))
                    = ∑ e ∈ Finset.Icc 1 N, (N : ℝ) * (1 / (e : ℝ)) := by
                        apply Finset.sum_congr rfl
                        intro e he
                        ring
                _ = (N : ℝ) * (∑ e ∈ Finset.Icc 1 N, (1 : ℝ) / (e : ℝ)) := by
                        rw [Finset.mul_sum]
      _ ≤ 8 * ((N : ℝ) * (1 + Real.log ((N : ℝ) + 1))) := by
              have hsum : (∑ e ∈ Finset.Icc 1 N, (1 : ℝ) / (e : ℝ)) ≤
                  1 + Real.log ((N : ℝ) + 1) := sum_inv_le_one_add_log N hN
              have hstep : (N : ℝ) * (∑ e ∈ Finset.Icc 1 N, (1 : ℝ) / (e : ℝ)) ≤
                  (N : ℝ) * (1 + Real.log ((N : ℝ) + 1)) :=
                mul_le_mul_of_nonneg_left hsum hN0
              exact mul_le_mul_of_nonneg_left hstep (by norm_num)
  calc
    ((Finset.Icc (-(N : ℤ)) (N : ℤ)).sum (fun d =>
      (Finset.Icc (-(N : ℤ)) (N : ℤ)).sum (fun g =>
        if (d, g) = (0, 0) then (0 : ℝ)
        else ((Int.gcd d.natAbs g.natAbs : ℝ) / (max d.natAbs g.natAbs : ℝ)))))
        = (∑ d ∈ G, ∑ g ∈ G, val d.natAbs g.natAbs) := by
            change (∑ d ∈ G, ∑ g ∈ G,
              if (d, g) = (0, 0) then (0 : ℝ)
              else ((Int.gcd d.natAbs g.natAbs : ℝ) / (max d.natAbs g.natAbs : ℝ)))
              = ∑ d ∈ G, ∑ g ∈ G, val d.natAbs g.natAbs
            apply Finset.sum_congr rfl
            intro d hd
            apply Finset.sum_congr rfl
            intro g hg
            rw [term_if_eq]
            unfold term val
            rw [int_gcd_natAbs]
    _ ≤ (∑ d ∈ G, ∑ g ∈ G, ub N d.natAbs g.natAbs) := by
            apply Finset.sum_le_sum
            intro d hd
            apply Finset.sum_le_sum
            intro g hg
            exact val_le_ub N d.natAbs g.natAbs (hmemN d hd) (hmemN g hg)
    _ = (∑ e ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
          ∑ g ∈ Finset.Icc (-(N : ℤ)) (N : ℤ),
            if e ∣ d.natAbs ∧ e ∣ g.natAbs then (e : ℝ) / (max d.natAbs g.natAbs : ℝ) else 0) := by
            change (∑ d ∈ G, ∑ g ∈ G, ub N d.natAbs g.natAbs) =
              ∑ e ∈ Finset.Icc 1 N, ∑ d ∈ G, ∑ g ∈ G,
                if e ∣ d.natAbs ∧ e ∣ g.natAbs then (e : ℝ) / (max d.natAbs g.natAbs : ℝ) else 0
            exact grid_ub_sum N
    _ = (∑ e ∈ Finset.Icc 1 N, ∑ d ∈ Finset.Icc (-((N / e : ℕ) : ℤ)) ((N / e : ℕ) : ℤ),
          ∑ g ∈ Finset.Icc (-((N / e : ℕ) : ℤ)) ((N / e : ℕ) : ℤ),
            (1 : ℝ) / (max d.natAbs g.natAbs : ℝ)) := by
            apply Finset.sum_congr rfl
            intro e he
            have he1 : 1 ≤ e := (Finset.mem_Icc.mp he).1
            exact inner_eq N e he1
    _ = (∑ e ∈ Finset.Icc 1 N, 8 * ((N / e : ℕ) : ℝ)) := by
            apply Finset.sum_congr rfl
            intro e he
            exact grid_inv_max_sum (N / e)
    _ ≤ 8 * (N : ℝ) * (1 + Real.log ((N : ℝ) + 1)) := by
            rw [mul_assoc]
            exact hmain
    _ ≤ 1000 * (N : ℝ) * (1 + Real.log ((N : ℝ) + 1)) := by
            have hx : 0 ≤ 1 + Real.log ((N : ℝ) + 1) := by linarith
            have h8 : 8 * (N : ℝ) ≤ 1000 * (N : ℝ) := by nlinarith
            exact mul_le_mul_of_nonneg_right h8 hx

end Commons.Data.Int