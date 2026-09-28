import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.MDEstimates.eNorm_sub_le
import Submission.Work.HP.MDBasic.finite_sets
import Submission.Work.HP.Q44Child.CountDefs
import Submission.Work.HP.Q44Child.quartic_zero_bound

/-!
# The lattice zero count for quartic threefolds (`Work.HP.Q44Child.latZeroCount`)
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

namespace Work.HP.Q44Child

open Work.HP MvPolynomial

/-! ## 0.  Helper lemmas (norms, combinatorics, arithmetic, Schwartz--Zippel) -/

/-- `eNorm (c • v) = |c| · eNorm v` for an integer scalar. -/
lemma eNorm_smul_int {ι : Type*} [Fintype ι] (c : ℤ) (v : ι → ℤ) :
    eNorm (c • v) = |(c : ℝ)| * eNorm v := by
  have hsum : (∑ i, (((c • v) i : ℤ) : ℝ) ^ 2) = (c : ℝ) ^ 2 * ∑ i, ((v i : ℤ) : ℝ) ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    push_cast
    ring
  rw [eNorm, hsum, Real.sqrt_mul (sq_nonneg (c : ℝ)), Real.sqrt_sq_eq_abs]
  rfl

/-- Triangle inequality for `eNorm`. -/
lemma eNorm_add_le {ι : Type*} [Fintype ι] (v w : ι → ℤ) :
    eNorm (v + w) ≤ eNorm v + eNorm w := by
  have h := MDEstimates.eNorm_sub_le v (-w)
  simpa [sub_neg_eq_add, eNorm_neg] using h

/-- If a finite set `S ⊆ ℤ` has all pairwise differences bounded by `R ≥ 0`, then
`#S ≤ R + 1`. -/
lemma ncard_le_of_pairwise_le (S : Set ℤ) {R : ℝ} (hR : 0 ≤ R) (hfin : S.Finite)
    (h : ∀ a ∈ S, ∀ b ∈ S, |(a : ℝ) - (b : ℝ)| ≤ R) :
    (S.ncard : ℝ) ≤ R + 1 := by
  rcases S.eq_empty_or_nonempty with hS | hne
  · rw [hS]; simp; linarith
  · obtain ⟨lo, hloS, hlomin⟩ := Set.exists_min_image S (fun x : ℤ => x) hfin hne
    have hsub : S ⊆ (↑(Finset.Icc lo (lo + ⌊R⌋)) : Set ℤ) := by
      intro x hx
      rw [Finset.mem_coe, Finset.mem_Icc]
      refine ⟨hlomin x hx, ?_⟩
      have hxR : ((x - lo : ℤ) : ℝ) ≤ R := by
        have hh := h x hx lo hloS
        have hcast : ((x - lo : ℤ) : ℝ) = (x : ℝ) - (lo : ℝ) := by push_cast; ring
        rw [hcast]
        exact (le_abs_self _).trans hh
      have h2 : (x - lo : ℤ) ≤ ⌊R⌋ := Int.le_floor.mpr hxR
      omega
    have hcard1 : (S.ncard : ℝ) ≤ ((Finset.Icc lo (lo + ⌊R⌋)).card : ℝ) := by
      have h' := Set.ncard_le_ncard hsub (Finset.finite_toSet _)
      rw [Set.ncard_coe_finset] at h'
      exact_mod_cast h'
    have hcard2 : ((Finset.Icc lo (lo + ⌊R⌋)).card : ℝ) ≤ R + 1 := by
      have hZ : ((Finset.Icc lo (lo + ⌊R⌋)).card : ℤ) = ⌊R⌋ + 1 := by
        rw [Int.card_Icc_of_le lo (lo + ⌊R⌋)
          (by have hfl : (0 : ℤ) ≤ ⌊R⌋ := Int.le_floor.mpr (by push_cast; exact hR); omega)]
        ring
      have hcast : ((Finset.Icc lo (lo + ⌊R⌋)).card : ℝ)
          = (((Finset.Icc lo (lo + ⌊R⌋)).card : ℤ) : ℝ) := by rw [Int.cast_natCast]
      rw [hcast, hZ]
      push_cast
      linarith [Int.floor_le R]
    linarith [hcard1, hcard2]

/-- A nonzero bivariate quartic over `ℤ` has `O(N)` zeros in the box `[-N,N]²`.  (We use the
crude constant `16` produced by the fibre induction of `step_aux`; only a fixed constant is
needed.) -/
theorem bivariate_quartic_zero_count (q : MvPolynomial (Fin 2) ℤ) (hq : q ≠ 0)
    (hdeg : q.totalDegree ≤ 4) (N : ℕ) :
    (Cnt 2 q N : ℝ) ≤ 16 * ((N : ℝ) + 1) := by
  have h := step_aux 0 (C := 4) (by norm_num)
    (fun g hg hgd M => by
      have h1 := count_one g hg hgd M
      have h2 : ((Cnt 1 g M : ℕ) : ℝ) ≤ 4 := by exact_mod_cast h1
      simpa using h2)
    q hq hdeg N
  have he : (4 * (2 : ℝ) ^ (0 + 1) + 2 * 4) * ((N : ℝ) + 1) ^ (0 + 1) = 16 * ((N : ℝ) + 1) := by
    norm_num
  rw [he] at h
  exact h

/-- Arithmetic assembly for the lattice zero count. -/
theorem arith_bound (N p q : ℝ) (hN : 0 ≤ 2 * N + 1) (hNq : 2 * N + 1 ≤ 35 * (1 + q))
    (hN1 : N + 1 ≤ 17 * (1 + q)) (hp : 0 ≤ p) (hq : 0 ≤ q) (hpq : q ≤ p) :
    4 * (2 * N + 1) ^ 2 + (2 * p + 1) * (16 * (N + 1)) ≤ 1000000 * (1 + p) * (1 + q) := by
  have h1q : 0 ≤ 1 + q := by linarith
  have h1p : 0 ≤ 1 + p := by linarith
  have hpq1 : 1 + q ≤ 1 + p := by linarith
  have hB : 0 ≤ 2 * p + 1 := by linarith
  have hA : (1 + q) * (1 + q) ≤ (1 + p) * (1 + q) := mul_le_mul_of_nonneg_right hpq1 h1q
  have hC : (2 * p + 1) * (1 + q) ≤ 3 * (1 + p) * (1 + q) :=
    mul_le_mul_of_nonneg_right (by linarith : 2 * p + 1 ≤ 3 * (1 + p)) h1q
  have hsq : (2 * N + 1) ^ 2 ≤ 1225 * ((1 + q) * (1 + q)) := by nlinarith [hN, hNq, h1q]
  have hD : (2 * p + 1) * (16 * (N + 1)) ≤ 272 * ((2 * p + 1) * (1 + q)) := by
    nlinarith [hB, hN1, h1q]
  have hP : 0 ≤ (1 + p) * (1 + q) := by positivity
  nlinarith [hsq, hA, hC, hD, hB, h1p, h1q, hP]

/-! ## 1.  The main counting statement -/

/-- **Counting step for `latZero_bound`.**  Let `b : Fin 3 → ℤ^5` be a `ℤ`-basis of `L ⊆ ℤ^5`
with `b 0` of minimal norm in `L∖{0}`.  Suppose the first two coordinates of `x = c₀b₀+c₁b₁+c₂b₂`
satisfy the *coefficient bounds* `|c₁| l₂ ≤ 16‖x‖`, `|c₂| l₃ ≤ 16‖x‖` with `0 < l₂ ≤ l₃` and
`‖b₀‖ ≤ l₂`.  If the quartic form `a` does not vanish identically on `L`, then for `Z ≥ 1` the
number of lattice points of `L` of norm at most `Z` at which `a` vanishes is
`≪ (1 + Z/‖b₀‖)(1 + Z/l₂)`. -/
theorem latZeroCount (b : Fin 3 → (Fin 5 → ℤ)) (a : Work.HP.Mon 4 4 → ℤ)
    (L : Submodule ℤ (Fin 5 → ℤ))
    (hb : LinearIndependent ℤ b) (hspan : Submodule.span ℤ (Set.range b) = L)
    (hb₀min : ∀ y ∈ L, y ≠ 0 → Work.HP.eNorm (b 0) ≤ Work.HP.eNorm y)
    (hne : ¬ (∀ u ∈ L, Work.HP.formEval 4 4 a u = 0))
    (l2 l3 : ℝ) (h2 : 0 < l2) (h3 : 0 < l3) (h23 : l2 ≤ l3)
    (hb0l2 : Work.HP.eNorm (b 0) ≤ l2)
    (hbound : ∀ c : Fin 3 → ℤ,
        |(c 1 : ℝ)| * l2 ≤ 16 * Work.HP.eNorm (∑ j, c j • b j) ∧
        |(c 2 : ℝ)| * l3 ≤ 16 * Work.HP.eNorm (∑ j, c j • b j))
    (Z : ℝ) (hZ : 1 ≤ Z) :
    (({x : Fin 5 → ℤ | x ∈ L ∧ Work.HP.eNorm x ≤ Z ∧ Work.HP.formEval 4 4 a x = 0} :
      Set (Fin 5 → ℤ)).ncard : ℝ)
      ≤ 1000000 * (1 + Z / Work.HP.eNorm (b 0)) * (1 + Z / l2) := by
  classical
  -- basic scalars
  have hmpos : 0 < eNorm (b 0) := eNorm_pos_of_ne_zero (hb.ne_zero 0)
  have hZnn : (0 : ℝ) ≤ Z := by linarith
  set m : ℝ := eNorm (b 0) with hm
  have hmp : 0 < m := by rw [hm]; exact hmpos
  have hb0l2' : m ≤ l2 := by rw [hm]; exact hb0l2
  -- the coordinate map
  set phi : (Fin 3 → ℤ) → (Fin 5 → ℤ) := (fun c => ∑ j, c j • b j) with hphi
  have hphi_apply : ∀ c : Fin 3 → ℤ, phi c = ∑ j, c j • b j := fun c => congrFun hphi c
  have hphi_inj : Function.Injective phi := by
    intro c c' h
    have h' : Fintype.linearCombination ℤ b c = Fintype.linearCombination ℤ b c' := by
      simpa [hphi, hphi_apply, Fintype.linearCombination_apply] using h
    have hz : Fintype.linearCombination ℤ b (c - c') = 0 := by
      rw [map_sub, h', sub_self]
    rw [Fintype.linearCombination_apply] at hz
    have hd := (Fintype.linearIndependent_iff.mp hb) (c - c') hz
    funext i
    exact sub_eq_zero.mp (by simpa using hd i)
  have hmemL : ∀ c : Fin 3 → ℤ, phi c ∈ L := by
    intro c
    rw [← hspan, Submodule.mem_span_range_iff_exists_fun ℤ]
    exact ⟨c, by simp [hphi_apply]⟩
  -- the substituted polynomial `G`
  set g : Fin 5 → MvPolynomial (Fin 3) ℤ :=
    (fun i => ∑ j : Fin 3, MvPolynomial.X j * MvPolynomial.C ((b j) i)) with hg
  set G : MvPolynomial (Fin 3) ℤ := MvPolynomial.aeval g (formZ a) with hG
  have haeval_eval : ∀ (c : Fin 3 → ℤ) (qp : MvPolynomial (Fin 5) ℤ),
      MvPolynomial.eval c (MvPolynomial.aeval g qp)
        = MvPolynomial.eval (fun i => MvPolynomial.eval c (g i)) qp := by
    intro c qp
    rw [MvPolynomial.aeval_def, ← MvPolynomial.C_eq_algebraMap]
    exact (MvPolynomial.eval₂_assoc (f := RingHom.id ℤ) (g := c) (q := g) (p := qp)).symm
  have hgi : ∀ (c : Fin 3 → ℤ), (fun i : Fin 5 => MvPolynomial.eval c (g i)) = phi c := by
    intro c
    funext i
    rw [hphi_apply c]
    simp only [hg, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul,
      MvPolynomial.eval_X, MvPolynomial.eval_C]
  have hevalG : ∀ c : Fin 3 → ℤ, MvPolynomial.eval c G = formEval 4 4 a (phi c) := by
    intro c
    rw [hG, haeval_eval, hgi c, eval_formZ]
  have hGne : G ≠ 0 := by
    intro h0
    apply hne
    intro u hu
    have hu' : u ∈ Submodule.span ℤ (Set.range b) := by rw [hspan]; exact hu
    rw [Submodule.mem_span_range_iff_exists_fun ℤ] at hu'
    obtain ⟨c, hc⟩ := hu'
    have hphic : phi c = u := by rw [hphi_apply c]; exact hc
    have hz : formEval 4 4 a u = 0 := by
      rw [← hphic, ← hevalG c]
      simp [h0]
    exact hz
  have hGdeg : G.totalDegree ≤ 4 := by
    have hform : (formZ a).IsHomogeneous 4 := by
      have h := MvPolynomial.IsHomogeneous.sum (Finset.univ : Finset (Mon 4 4))
        (fun mm : Mon 4 4 => MvPolynomial.monomial mm.toFinsupp (a mm)) 4
        (fun mm _ => MvPolynomial.isHomogeneous_monomial (a mm) (Mon_degree_toFinsupp mm))
      simpa [formZ] using h
    have hg1 : ∀ i, (g i).IsHomogeneous 1 := by
      intro i
      have h := MvPolynomial.IsHomogeneous.sum (Finset.univ : Finset (Fin 3))
        (fun j : Fin 3 => MvPolynomial.X j * MvPolynomial.C ((b j) i)) 1
        (fun j _ => by
          simpa [mul_comm] using MvPolynomial.isHomogeneous_C_mul_X ((b j) i) j)
      simpa [hg] using h
    have h := hform.aeval g hg1
    rw [hG]
    simpa using h.totalDegree_le
  -- the coefficient set `T`
  set T : Set (Fin 3 → ℤ) :=
    {c | eNorm (phi c) ≤ Z ∧ MvPolynomial.eval c G = 0} with hT
  have hmemT : ∀ c : Fin 3 → ℤ, c ∈ T ↔ eNorm (phi c) ≤ Z ∧ MvPolynomial.eval c G = 0 :=
    fun c => by simp only [hT, Set.mem_setOf_eq]
  have hST : ({x : Fin 5 → ℤ | x ∈ L ∧ eNorm x ≤ Z ∧ formEval 4 4 a x = 0} :
      Set (Fin 5 → ℤ)) = phi '' T := by
    ext x
    constructor
    · rintro ⟨hxL, hxZ, hx0⟩
      have hx' : x ∈ Submodule.span ℤ (Set.range b) := by rw [hspan]; exact hxL
      rw [Submodule.mem_span_range_iff_exists_fun ℤ] at hx'
      obtain ⟨c, hc⟩ := hx'
      have hphic : phi c = x := by rw [hphi_apply c]; exact hc
      refine ⟨c, ?_, hphic⟩
      rw [hmemT c]
      exact ⟨by rw [hphic]; exact hxZ, by rw [hevalG c, hphic]; exact hx0⟩
    · rintro ⟨c, hcT, rfl⟩
      exact ⟨hmemL c, (hmemT c).mp hcT |>.1, by rw [← hevalG c]; exact (hmemT c).mp hcT |>.2⟩
  have hcard : ({x : Fin 5 → ℤ | x ∈ L ∧ eNorm x ≤ Z ∧ formEval 4 4 a x = 0} :
      Set (Fin 5 → ℤ)).ncard = T.ncard := by
    rw [hST, Set.ncard_image_of_injective T hphi_inj]
  -- finiteness of `T`
  have hTfin : T.Finite := by
    have h1 : T ⊆ phi ⁻¹' {y : Fin 5 → ℤ | eNorm y ≤ Z} := fun c hc => (hmemT c).mp hc |>.1
    exact (Work.HP.MDBasic.finite_eNorm_le Z).preimage (fun a _ b _ h => hphi_inj h) |>.subset h1
  -- the box of tails
  set N2 : ℕ := ⌈16 * Z / l2⌉₊ with hN2
  set Bx : Finset (Fin 2 → ℤ) := cbox 2 N2 with hBx
  have hN2ge : 16 * Z / l2 ≤ (N2 : ℝ) := by rw [hN2]; exact Nat.le_ceil _
  have hN2lt : (N2 : ℝ) < 16 * Z / l2 + 1 := by
    rw [hN2]; exact Nat.ceil_lt_add_one (by positivity)
  have htail_mem : ∀ c ∈ T, Fin.tail c ∈ Bx := by
    intro c hc
    have hcZ : eNorm (phi c) ≤ Z := (hmemT c).mp hc |>.1
    have hbnd := hbound c
    rw [← hphi_apply c] at hbnd
    rw [hBx, mem_cbox]
    intro i
    have hle2 : |(c 1 : ℝ)| ≤ 16 * Z / l2 := by
      rw [le_div_iff₀ h2]
      nlinarith [hbnd.1, hcZ, mul_le_mul_of_nonneg_left hcZ (show (0:ℝ) ≤ 16 by norm_num)]
    have hle3 : |(c 2 : ℝ)| ≤ 16 * Z / l2 := by
      have h3' : |(c 2 : ℝ)| ≤ 16 * Z / l3 := by
        rw [le_div_iff₀ h3]
        nlinarith [hbnd.2, hcZ, mul_le_mul_of_nonneg_left hcZ (show (0:ℝ) ≤ 16 by norm_num)]
      refine h3'.trans ?_
      exact div_le_div_of_nonneg_left (by linarith : (0:ℝ) ≤ 16 * Z) h2 h23
    have key : ∀ t : ℤ, |(t : ℝ)| ≤ (N2 : ℝ) → -(N2 : ℤ) ≤ t ∧ t ≤ (N2 : ℤ) := by
      intro t ht
      have ht' : ((|t| : ℤ) : ℝ) ≤ ((N2 : ℤ) : ℝ) := by
        rw [Int.cast_abs]; push_cast; exact ht
      exact abs_le.mp (by exact_mod_cast ht')
    fin_cases i
    · show -(N2 : ℤ) ≤ c 1 ∧ c 1 ≤ (N2 : ℤ)
      exact key (c 1) (hle2.trans hN2ge)
    · show -(N2 : ℤ) ≤ c 2 ∧ c 2 ≤ (N2 : ℤ)
      exact key (c 2) (hle3.trans hN2ge)
  -- the fibre polynomial
  set p : Polynomial (MvPolynomial (Fin 2) ℤ) := MvPolynomial.finSuccEquiv ℤ 2 G with hp
  have hroot : ∀ (c : Fin 3 → ℤ), MvPolynomial.eval c G = 0 →
      Polynomial.eval (c 0) (Polynomial.map (MvPolynomial.eval (Fin.tail c)) p) = 0 := by
    intro c hc
    have hev := MvPolynomial.eval_eq_eval_mv_eval' (Fin.tail c) (c 0) G
    rw [Fin.cons_self_tail, ← hp] at hev
    rw [← hev]; exact hc
  -- per-fibre bounds
  have hgood : ∀ u ∈ Bx, Polynomial.map (MvPolynomial.eval u) p ≠ 0 →
      (T ∩ {c : Fin 3 → ℤ | Fin.tail c = u}).ncard ≤ 4 := by
    intro u _ hq
    set Pre : Set (Fin 3 → ℤ) := T ∩ {c : Fin 3 → ℤ | Fin.tail c = u} with hPre
    have hPrefin : Pre.Finite := hTfin.subset Set.inter_subset_left
    have hinj : Set.InjOn (fun c : Fin 3 → ℤ => c 0) Pre := by
      intro c hc c' hc' h
      have h' : c 0 = c' 0 := h
      have h1 : Fin.tail c = u := hc.2
      have h2 : Fin.tail c' = u := hc'.2
      rw [← Fin.cons_self_tail c, h1, h', ← h2, Fin.cons_self_tail c']
    have hSu : ((fun c : Fin 3 → ℤ => c 0) '' Pre).ncard = Pre.ncard := hinj.ncard_image
    have hSuFin : ((fun c : Fin 3 → ℤ => c 0) '' Pre).Finite := hPrefin.image _
    have hdeg : (Polynomial.map (MvPolynomial.eval u) p).natDegree ≤ 4 := by
      calc (Polynomial.map (MvPolynomial.eval u) p).natDegree
          ≤ p.natDegree := Polynomial.natDegree_map_le
        _ = MvPolynomial.degreeOf 0 G := by rw [hp, MvPolynomial.natDegree_finSuccEquiv]
        _ ≤ G.totalDegree := MvPolynomial.degreeOf_le_totalDegree G 0
        _ ≤ 4 := hGdeg
    have hsub : ((fun c : Fin 3 → ℤ => c 0) '' Pre)
        ⊆ (↑(Polynomial.map (MvPolynomial.eval u) p).roots.toFinset : Set ℤ) := by
      rintro t ⟨c, hc, rfl⟩
      rw [Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_roots hq, Polynomial.IsRoot.def]
      have hc'' : MvPolynomial.eval c G = 0 := ((hmemT c).mp hc.1).2
      have hcu : Fin.tail c = u := hc.2
      rw [← hcu]
      exact hroot c hc''
    calc Pre.ncard = ((fun c : Fin 3 → ℤ => c 0) '' Pre).ncard := hSu.symm
      _ ≤ (↑(Polynomial.map (MvPolynomial.eval u) p).roots.toFinset : Set ℤ).ncard :=
            Set.ncard_le_ncard hsub (Finset.finite_toSet _)
      _ ≤ 4 := by
            rw [Set.ncard_coe_finset]
            exact Work.Q44Child.roots_card_le _ hq hdeg
  have hbad : ∀ u ∈ Bx, Polynomial.map (MvPolynomial.eval u) p = 0 →
      ((T ∩ {c : Fin 3 → ℤ | Fin.tail c = u}).ncard : ℝ) ≤ 2 * Z / m + 1 := by
    intro u _ _
    set Pre : Set (Fin 3 → ℤ) := T ∩ {c : Fin 3 → ℤ | Fin.tail c = u} with hPre
    have hPrefin : Pre.Finite := hTfin.subset Set.inter_subset_left
    have hinj : Set.InjOn (fun c : Fin 3 → ℤ => c 0) Pre := by
      intro c hc c' hc' h
      have h' : c 0 = c' 0 := h
      have h1 : Fin.tail c = u := hc.2
      have h2 : Fin.tail c' = u := hc'.2
      rw [← Fin.cons_self_tail c, h1, h', ← h2, Fin.cons_self_tail c']
    have hSu : ((fun c : Fin 3 → ℤ => c 0) '' Pre).ncard = Pre.ncard := hinj.ncard_image
    have hSuFin : ((fun c : Fin 3 → ℤ => c 0) '' Pre).Finite := hPrefin.image _
    have hpair : ∀ a ∈ ((fun c : Fin 3 → ℤ => c 0) '' Pre),
        ∀ b ∈ ((fun c : Fin 3 → ℤ => c 0) '' Pre), |(a : ℝ) - (b : ℝ)| ≤ 2 * Z / m := by
      rintro a ⟨c, hc, rfl⟩ b ⟨c', hc', rfl⟩
      show |(c 0 : ℝ) - (c' 0 : ℝ)| ≤ 2 * Z / m
      have hcT : c ∈ T ∧ Fin.tail c = u := hc
      have hc'T : c' ∈ T ∧ Fin.tail c' = u := hc'
      have hcZ : eNorm (phi c) ≤ Z := (hmemT c).mp hcT.1 |>.1
      have hc'Z : eNorm (phi c') ≤ Z := (hmemT c').mp hc'T.1 |>.1
      have hstep : ∀ d : Fin 3 → ℤ,
          phi d = d 0 • b 0 + ((Fin.tail d) 0) • b 1 + ((Fin.tail d) 1) • b 2 := by
        intro d
        rw [hphi_apply d, Fin.sum_univ_three]
        rfl
      have hdiff : phi c - phi c' = (c 0 - c' 0) • b 0 := by
        rw [hstep c, hstep c', hcT.2, hc'T.2]
        module
      have h4 : eNorm (phi c - phi c') = |(c 0 : ℝ) - (c' 0 : ℝ)| * m := by
        rw [hdiff, eNorm_smul_int, ← hm]
        congr 1
        push_cast; ring
      have htri : eNorm (phi c - phi c') ≤ eNorm (phi c) + eNorm (phi c') :=
        MDEstimates.eNorm_sub_le _ _
      rw [le_div_iff₀ hmp]
      rw [← h4]
      linarith
    have hmain := ncard_le_of_pairwise_le ((fun c : Fin 3 → ℤ => c 0) '' Pre)
      (R := 2 * Z / m) (by positivity) hSuFin hpair
    rw [hSu] at hmain
    exact hmain
  -- the fibre sum
  have hcover : T ⊆ ⋃ u ∈ Bx, T ∩ {c : Fin 3 → ℤ | Fin.tail c = u} := by
    intro c hc
    refine Set.mem_iUnion.mpr ⟨Fin.tail c, ?_⟩
    exact Set.mem_iUnion.mpr ⟨htail_mem c hc, hc, rfl⟩
  have hUnion_fin : (⋃ u ∈ Bx, T ∩ {c : Fin 3 → ℤ | Fin.tail c = u}).Finite :=
    hTfin.subset (Set.iUnion_subset fun u => Set.iUnion_subset fun _ => Set.inter_subset_left)
  have hstep1 : T.ncard ≤ (⋃ u ∈ Bx, T ∩ {c : Fin 3 → ℤ | Fin.tail c = u}).ncard :=
    Set.ncard_le_ncard hcover hUnion_fin
  have hstep2 : (⋃ u ∈ Bx, T ∩ {c : Fin 3 → ℤ | Fin.tail c = u}).ncard
      ≤ ∑ u ∈ Bx, (T ∩ {c : Fin 3 → ℤ | Fin.tail c = u}).ncard :=
    Finset.set_ncard_biUnion_le Bx _
  have hpointwise : ∀ u ∈ Bx, ((T ∩ {c : Fin 3 → ℤ | Fin.tail c = u}).ncard : ℝ)
      ≤ 4 + (2 * Z / m + 1) *
          (if Polynomial.map (MvPolynomial.eval u) p = 0 then (1 : ℝ) else 0) := by
    intro u hu
    by_cases hb0 : Polynomial.map (MvPolynomial.eval u) p = 0
    · rw [if_pos hb0]
      have hA : (0 : ℝ) ≤ 2 * Z / m + 1 := by positivity
      have := hbad u hu hb0
      linarith
    · rw [if_neg hb0]
      have h4 := hgood u hu hb0
      have h4' : ((T ∩ {c : Fin 3 → ℤ | Fin.tail c = u}).ncard : ℝ) ≤ 4 := by exact_mod_cast h4
      linarith
  have hsum : (∑ u ∈ Bx, ((T ∩ {c : Fin 3 → ℤ | Fin.tail c = u}).ncard : ℝ))
      ≤ 4 * (Bx.card : ℝ) + (2 * Z / m + 1) *
          ((Bx.filter (fun u => Polynomial.map (MvPolynomial.eval u) p = 0)).card : ℝ) := by
    have h1 := Finset.sum_le_sum hpointwise
    have h2a : (∑ u ∈ Bx, (4 : ℝ)) = 4 * (Bx.card : ℝ) := by
      rw [Finset.sum_const, nsmul_eq_mul]; ring
    have h2b : (∑ u ∈ Bx, (2 * Z / m + 1) *
        (if Polynomial.map (MvPolynomial.eval u) p = 0 then (1 : ℝ) else 0))
        = (2 * Z / m + 1) *
          ((Bx.filter (fun u => Polynomial.map (MvPolynomial.eval u) p = 0)).card : ℝ) := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_boole]
    have h2 : (∑ u ∈ Bx, (4 + (2 * Z / m + 1) *
        (if Polynomial.map (MvPolynomial.eval u) p = 0 then (1 : ℝ) else 0)))
        = 4 * (Bx.card : ℝ) + (2 * Z / m + 1) *
          ((Bx.filter (fun u => Polynomial.map (MvPolynomial.eval u) p = 0)).card : ℝ) := by
      rw [Finset.sum_add_distrib, h2a, h2b]
    linarith [h1, h2]
  have hBxcard : (Bx.card : ℝ) = (2 * (N2 : ℝ) + 1) ^ 2 := by
    rw [hBx]; exact cbox_card 2 N2
  have hbadcard : ((Bx.filter (fun u => Polynomial.map (MvPolynomial.eval u) p = 0)).card : ℝ)
      ≤ 16 * ((N2 : ℝ) + 1) := by
    have hpne : p ≠ 0 := by
      intro h
      apply hGne
      exact (MvPolynomial.finSuccEquiv ℤ 2).injective (by rw [← hp]; exact h)
    obtain ⟨k, hk⟩ : ∃ k, p.coeff k ≠ 0 := by
      by_contra h
      push_neg at h
      exact hpne (Polynomial.ext h)
    have hk' : (MvPolynomial.finSuccEquiv ℤ 2 G).coeff k ≠ 0 := by rwa [hp] at hk
    have hkdeg : (p.coeff k).totalDegree ≤ 4 := by
      have h1 := MvPolynomial.totalDegree_coeff_finSuccEquiv_add_le G k hk'
      have h2 : ((MvPolynomial.finSuccEquiv ℤ 2 G).coeff k).totalDegree ≤ G.totalDegree :=
        (Nat.le_add_right _ _).trans h1
      rw [hp]; exact h2.trans hGdeg
    have hsub : Bx.filter (fun u => Polynomial.map (MvPolynomial.eval u) p = 0)
        ⊆ (cbox 2 N2).filter (fun u => MvPolynomial.eval u (p.coeff k) = 0) := by
      intro u hu
      rw [Finset.mem_filter] at hu ⊢
      refine ⟨by rw [hBx] at hu; exact hu.1, ?_⟩
      have hc := congrArg (fun q : Polynomial ℤ => q.coeff k) hu.2
      simpa [MvPolynomial.coeff_eval_eq_eval_coeff] using hc
    calc ((Bx.filter (fun u => Polynomial.map (MvPolynomial.eval u) p = 0)).card : ℝ)
        ≤ (((cbox 2 N2).filter (fun u => MvPolynomial.eval u (p.coeff k) = 0)).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ = (Cnt 2 (p.coeff k) N2 : ℝ) := rfl
      _ ≤ 16 * ((N2 : ℝ) + 1) := bivariate_quartic_zero_count (p.coeff k) hk hkdeg N2
  -- final numeric assembly
  have hTbound : (T.ncard : ℝ) ≤
      4 * (2 * (N2 : ℝ) + 1) ^ 2 + (2 * Z / m + 1) * (16 * ((N2 : ℝ) + 1)) := by
    have h1 : (T.ncard : ℝ)
        ≤ (∑ u ∈ Bx, ((T ∩ {c : Fin 3 → ℤ | Fin.tail c = u}).ncard : ℝ)) := by
      have ha : (T.ncard : ℝ)
          ≤ (((⋃ u ∈ Bx, T ∩ {c : Fin 3 → ℤ | Fin.tail c = u}).ncard : ℕ) : ℝ) := by
        exact_mod_cast hstep1
      have hb : (((⋃ u ∈ Bx, T ∩ {c : Fin 3 → ℤ | Fin.tail c = u}).ncard : ℕ) : ℝ)
          ≤ ((∑ u ∈ Bx, (T ∩ {c : Fin 3 → ℤ | Fin.tail c = u}).ncard : ℕ) : ℝ) := by
        exact_mod_cast hstep2
      have hc : (((∑ u ∈ Bx, (T ∩ {c : Fin 3 → ℤ | Fin.tail c = u}).ncard : ℕ) : ℝ))
          = ∑ u ∈ Bx, ((T ∩ {c : Fin 3 → ℤ | Fin.tail c = u}).ncard : ℝ) := by
        push_cast; ring
      linarith [ha, hb, hc]
    have hA : (0 : ℝ) ≤ 2 * Z / m + 1 := by positivity
    calc (T.ncard : ℝ)
        ≤ ∑ u ∈ Bx, ((T ∩ {c : Fin 3 → ℤ | Fin.tail c = u}).ncard : ℝ) := h1
      _ ≤ 4 * (Bx.card : ℝ) + (2 * Z / m + 1) *
            ((Bx.filter (fun u => Polynomial.map (MvPolynomial.eval u) p = 0)).card : ℝ) := hsum
      _ ≤ 4 * (2 * (N2 : ℝ) + 1) ^ 2 + (2 * Z / m + 1) * (16 * ((N2 : ℝ) + 1)) := by
            rw [hBxcard]
            nlinarith [hbadcard, hA, mul_le_mul_of_nonneg_left hbadcard hA]
  have hN2le : 2 * (N2 : ℝ) + 1 ≤ 35 * (1 + Z / l2) := by
    have hlt : (N2 : ℝ) < 16 * (Z / l2) + 1 := by
      have h := hN2lt
      rwa [mul_div_assoc] at h
    have hw : 0 ≤ Z / l2 := by positivity
    have hlt2 : 2 * (N2 : ℝ) + 1 < 32 * (Z / l2) + 3 := by linarith
    have hw2 : 32 * (Z / l2) + 3 ≤ 35 * (1 + Z / l2) := by nlinarith [hw]
    linarith
  have hN1 : (N2 : ℝ) + 1 ≤ 17 * (1 + Z / l2) := by
    have hlt : (N2 : ℝ) < 16 * (Z / l2) + 1 := by
      have h := hN2lt
      rwa [mul_div_assoc] at h
    have hw : 0 ≤ Z / l2 := by positivity
    linarith
  have hpq : Z / l2 ≤ Z / m := div_le_div_of_nonneg_left hZnn hmp hb0l2'
  have harith := arith_bound (N2 : ℝ) (Z / m) (Z / l2) (by positivity) hN2le hN1
    (by positivity) (by positivity) hpq
  have key : (T.ncard : ℝ) ≤ 1000000 * (1 + Z / m) * (1 + Z / l2) := by
    calc (T.ncard : ℝ)
        ≤ 4 * (2 * (N2 : ℝ) + 1) ^ 2 + (2 * Z / m + 1) * (16 * ((N2 : ℝ) + 1)) := hTbound
      _ = 4 * (2 * (N2 : ℝ) + 1) ^ 2 + (2 * (Z / m) + 1) * (16 * ((N2 : ℝ) + 1)) := by ring
      _ ≤ 1000000 * (1 + Z / m) * (1 + Z / l2) := harith
  rw [hcard]
  simpa only [hm] using key

end Work.HP.Q44Child
