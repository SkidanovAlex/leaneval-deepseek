import Mathlib
import Submission.Work.Q44Geom.homogeneousInterpolation
import Submission.Work.Q44Geom.factorizationHomogeneous

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

noncomputable section
open MvPolynomial

namespace Work.Q44Geom

abbrev H (n : ℕ) := MvPolynomial.homogeneousSubmodule (Fin 3) ℚ n

/-- The dimension of the space of degree-`m` forms in two variables, i.e. the value of the
Hilbert function of a complete intersection of degrees `a`, `b` at large degree. -/
def D (m : ℕ) : ℕ := (m + 1) * (m + 2) / 2

/-! ## 1. The dimension of the space of homogeneous forms of degree `n` -/

lemma degree_of_mem_finsuppAntidiag {n : ℕ} {f : Fin 3 →₀ ℕ}
    (hf : f ∈ (Finset.univ : Finset (Fin 3)).finsuppAntidiag n) : f.degree = n := by
  have h := (Finset.mem_finsuppAntidiag.mp hf).1
  rw [Finsupp.degree_eq_sum]
  simpa using h

noncomputable def monomialBasis (n : ℕ) :
    Module.Basis ↥((Finset.univ : Finset (Fin 3)).finsuppAntidiag n) ℚ (H n) := by
  rw [show H n = MvPolynomial.restrictSupport (σ := Fin 3) ℚ {d : Fin 3 →₀ ℕ | d.degree = n}
    from by
      change MvPolynomial.homogeneousSubmodule (Fin 3) ℚ n
        = MvPolynomial.restrictSupport (σ := Fin 3) ℚ {d : Fin 3 →₀ ℕ | d.degree = n}
      rw [MvPolynomial.restrictSupport, MvPolynomial.homogeneousSubmodule_eq_finsupp_supported]]
  exact (MvPolynomial.basisRestrictSupport (σ := Fin 3) ℚ {d : Fin 3 →₀ ℕ | d.degree = n}).reindex
    (Equiv.subtypeEquivRight (fun d => by
      rw [Finset.mem_finsuppAntidiag]
      constructor
      · intro h
        change d.degree = n
        rw [Finsupp.degree_eq_sum]
        simpa using h.1
      · intro h
        refine ⟨?_, Finset.subset_univ _⟩
        change d.degree = n at h
        rw [Finsupp.degree_eq_sum] at h
        simpa using h)).symm

instance instFiniteH (n : ℕ) : Module.Finite ℚ (H n) :=
  Module.Finite.of_basis (monomialBasis n)

instance instFiniteDimH (n : ℕ) : FiniteDimensional ℚ (H n) :=
  Module.Finite.of_basis (monomialBasis n)

theorem finrank_H (n : ℕ) : Module.finrank ℚ (H n) = D n := by
  have h1 : Module.finrank ℚ (H n)
      = Fintype.card ↥((Finset.univ : Finset (Fin 3)).finsuppAntidiag n) :=
    Module.finrank_eq_card_basis (monomialBasis n)
  rw [h1, Fintype.card_coe, Finset.card_finsuppAntidiag_nat_eq_choose,
    Finset.card_univ, Fintype.card_fin]
  rw [show 3 + n - 1 = n + 2 from by omega, D]
  have h2 : (n + 2).choose n = (n + 2).choose 2 := by
    rw [show n = n + 2 - 2 from by omega]
    exact Nat.choose_symm (by omega)
  rw [h2, Nat.choose_two_right, show n + 2 - 1 = n + 1 from by omega, Nat.mul_comm]

/-! ## 2. Homogeneity of a factor of a homogeneous product -/

lemma homogeneousComponent_mul_right {f w : MvPolynomial (Fin 3) ℚ} {a d : ℕ}
    (hfa : f.IsHomogeneous a) :
    MvPolynomial.homogeneousComponent (d + a) (w * f)
      = MvPolynomial.homogeneousComponent d w * f := by
  have hsub : w * f = ∑ e ∈ Finset.range (w.totalDegree + 1),
      MvPolynomial.homogeneousComponent e w * f := by
    rw [← Finset.sum_mul, MvPolynomial.sum_homogeneousComponent]
  rw [hsub, map_sum]
  rw [Finset.sum_eq_single d]
  · rw [MvPolynomial.homogeneousComponent_of_mem
      ((MvPolynomial.homogeneousComponent_mem d w).mul hfa)]
    rw [if_pos rfl]
  · intro e _ he
    rw [MvPolynomial.homogeneousComponent_of_mem
      ((MvPolynomial.homogeneousComponent_mem e w).mul hfa)]
    rw [if_neg (show ¬(d + a = e + a) from by omega)]
  · intro hd
    have h0 : MvPolynomial.homogeneousComponent d w = 0 :=
      MvPolynomial.homogeneousComponent_eq_zero d w (by rw [Finset.mem_range] at hd; omega)
    rw [h0, zero_mul, map_zero]

lemma isHomogeneous_of_mul_right {f w : MvPolynomial (Fin 3) ℚ} {M a : ℕ} (hf : f ≠ 0)
    (hfa : f.IsHomogeneous a) (h : (w * f).IsHomogeneous M) : w.IsHomogeneous (M - a) := by
  by_cases hw : w = 0
  · rw [hw]; exact MvPolynomial.isHomogeneous_zero (Fin 3) ℚ (M - a)
  have hvan : ∀ d : ℕ, d ≠ M - a → MvPolynomial.homogeneousComponent d w = 0 := by
    intro d hd
    have h1 : MvPolynomial.homogeneousComponent (d + a) (w * f) = 0 := by
      rw [MvPolynomial.homogeneousComponent_of_mem h]
      rw [if_neg (show ¬(d + a = M) from by omega)]
    rw [homogeneousComponent_mul_right hfa] at h1
    exact (mul_eq_zero.mp h1).resolve_right hf
  have hle : M - a ≤ w.totalDegree := by
    by_contra hcon
    rw [not_le] at hcon
    exact hw (by
      rw [← MvPolynomial.sum_homogeneousComponent (φ := w)]
      refine Finset.sum_eq_zero fun d hd => hvan d (by
        have hd' : d ≤ w.totalDegree := by
          rw [Finset.mem_range] at hd; omega
        omega))
  rw [← MvPolynomial.sum_homogeneousComponent (φ := w)]
  rw [Finset.sum_eq_single (M - a)]
  · exact MvPolynomial.homogeneousComponent_mem (M - a) w
  · intro d _ hd; exact hvan d hd
  · intro h; exact absurd (Finset.mem_range.mpr (by omega)) h

/-! ## 3. Coprimality consequences -/

lemma dvd_of_dvd_mul_of_coprime {f g v : MvPolynomial (Fin 3) ℚ} (hf : f ≠ 0)
    (hcop : ∀ h, h ∣ f → h ∣ g → IsUnit h) (h : f ∣ v * g) : f ∣ v := by
  have h' : f ∣ g * v := by simpa [mul_comm] using h
  refine UniqueFactorizationMonoid.dvd_of_dvd_mul_right_of_no_prime_factors hf ?_ h'
  intro d hdf hdg hp
  exact hp.not_isUnit (hcop d hdf hdg)

/-! ## 4. The multiplication map `(u, v) ↦ u * f + v * g` on graded pieces -/

def mulMap (f g : MvPolynomial (Fin 3) ℚ) (a b n : ℕ) (hfa : f.IsHomogeneous a)
    (hgb : g.IsHomogeneous b) (hn : a + b ≤ n) : H (n - a) × H (n - b) →ₗ[ℚ] H n where
  toFun p := ⟨(p.1 : MvPolynomial (Fin 3) ℚ) * f + (p.2 : MvPolynomial (Fin 3) ℚ) * g, by
    have ha : a ≤ n := le_trans (Nat.le_add_right a b) hn
    have hb : b ≤ n := le_trans (Nat.le_add_left b a) hn
    have h1 : ((p.1 : MvPolynomial (Fin 3) ℚ) * f).IsHomogeneous ((n - a) + a) := p.1.2.mul hfa
    have h2 : ((p.2 : MvPolynomial (Fin 3) ℚ) * g).IsHomogeneous ((n - b) + b) := p.2.2.mul hgb
    rw [Nat.sub_add_cancel ha] at h1
    rw [Nat.sub_add_cancel hb] at h2
    exact h1.add h2⟩
  map_add' p q := by
    apply Subtype.ext
    simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, add_mul]
    ring
  map_smul' c p := by
    apply Subtype.ext
    simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, smul_add, smul_mul_assoc,
      RingHom.id_apply]

def koszulMap (f g : MvPolynomial (Fin 3) ℚ) (a b n : ℕ) (hfa : f.IsHomogeneous a)
    (hgb : g.IsHomogeneous b) (hn : a + b ≤ n) : H (n - a - b) →ₗ[ℚ] H (n - a) × H (n - b) where
  toFun w :=
    (⟨-((w : MvPolynomial (Fin 3) ℚ) * g), by
        have hb : b ≤ n - a := by omega
        have h := ((w.2.mul hgb).neg)
        rwa [Nat.sub_add_cancel hb] at h⟩,
     ⟨(w : MvPolynomial (Fin 3) ℚ) * f, by
        have h := w.2.mul hfa
        rw [show (n - a - b) + a = n - b from by omega] at h
        exact h⟩)
  map_add' p q := by
    apply Prod.ext <;> · apply Subtype.ext
                         simp only [Prod.fst_add, Prod.snd_add, Submodule.coe_add, add_mul]
                         try ring
  map_smul' c p := by
    apply Prod.ext
    · apply Subtype.ext
      simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, smul_neg, smul_mul_assoc,
        RingHom.id_apply]
    · apply Subtype.ext
      simp only [Prod.smul_fst, Prod.smul_snd, Submodule.coe_smul, smul_mul_assoc,
        RingHom.id_apply]

theorem ker_mulMap_eq_range_koszulMap {f g : MvPolynomial (Fin 3) ℚ} {a b n : ℕ}
    (hf : f ≠ 0) (hfa : f.IsHomogeneous a) (hgb : g.IsHomogeneous b)
    (hcop : ∀ h, h ∣ f → h ∣ g → IsUnit h) (hn : a + b ≤ n) :
    (mulMap f g a b n hfa hgb hn).ker = (koszulMap f g a b n hfa hgb hn).range := by
  refine le_antisymm ?_ ?_
  · intro x hx
    rw [LinearMap.mem_ker] at hx
    have h0 : (x.1 : MvPolynomial (Fin 3) ℚ) * f + (x.2 : MvPolynomial (Fin 3) ℚ) * g = 0 := by
      have := congrArg (fun y : H n => (y : MvPolynomial (Fin 3) ℚ)) hx
      simpa [mulMap] using this
    have hdvd : f ∣ (x.2 : MvPolynomial (Fin 3) ℚ) * g :=
      ⟨-(x.1 : MvPolynomial (Fin 3) ℚ), by linear_combination h0⟩
    obtain ⟨w, hw⟩ := dvd_of_dvd_mul_of_coprime hf hcop hdvd
    have hx1 : (x.1 : MvPolynomial (Fin 3) ℚ) = -(w * g) := by
      have h1 : f * ((x.1 : MvPolynomial (Fin 3) ℚ) + w * g) = 0 := by
        rw [hw] at h0
        linear_combination h0
      rcases mul_eq_zero.mp h1 with h2 | h2
      · exact absurd h2 hf
      · linear_combination h2
    have hx2 : (x.2 : MvPolynomial (Fin 3) ℚ) = w * f := by rw [hw, mul_comm]
    have hwdeg : w.IsHomogeneous (n - a - b) := by
      have h1 : (w * f).IsHomogeneous (n - b) := by
        rw [← hx2]
        exact x.2.2
      have h2 := isHomogeneous_of_mul_right hf hfa h1
      rwa [show n - b - a = n - a - b from by omega] at h2
    refine ⟨⟨w, hwdeg⟩, ?_⟩
    apply Prod.ext
    · apply Subtype.ext
      simpa [koszulMap] using hx1.symm
    · apply Subtype.ext
      simpa [koszulMap] using hx2.symm
  · rintro x ⟨w, rfl⟩
    rw [LinearMap.mem_ker]
    apply Subtype.ext
    show -((w : MvPolynomial (Fin 3) ℚ) * g) * f + ((w : MvPolynomial (Fin 3) ℚ) * f) * g = 0
    ring

/-! ## 5. The codimension bound -/

lemma D_arith' (a b k : ℕ) :
    D (a + b + k) + D k = D (b + k) + D (a + k) + a * b := by
  have htwo : ∀ m : ℕ, 2 * D m = (m + 1) * (m + 2) := by
    intro m
    rw [D, Nat.mul_div_cancel']
    exact even_iff_two_dvd.mp (by
      simpa [Nat.add_assoc] using Nat.even_mul_succ_self (m + 1))
  apply Nat.mul_left_cancel (show 0 < 2 by norm_num)
  rw [Nat.mul_add, Nat.mul_add, Nat.mul_add, htwo, htwo, htwo, htwo]
  ring

lemma D_arith (a b n : ℕ) (hn : a + b ≤ n) :
    D n + D (n - a - b) = D (n - a) + D (n - b) + a * b := by
  generalize hk : n - a - b = k
  have e1 : n = a + b + k := by omega
  rw [e1]
  rw [show a + b + k - a = b + k from by omega,
    show a + b + k - b = a + k from by omega]
  exact D_arith' a b k

theorem finrank_quot_mulMap_le {f g : MvPolynomial (Fin 3) ℚ} {a b n : ℕ}
    (hf : f ≠ 0) (hfa : f.IsHomogeneous a) (hgb : g.IsHomogeneous b)
    (hcop : ∀ h, h ∣ f → h ∣ g → IsUnit h) (hn : a + b ≤ n) :
    Module.finrank ℚ (H n ⧸ (mulMap f g a b n hfa hgb hn).range) ≤ a * b := by
  have hA := Submodule.finrank_quotient_add_finrank (mulMap f g a b n hfa hgb hn).range
  have hB := LinearMap.finrank_range_add_finrank_ker (mulMap f g a b n hfa hgb hn)
  have hC : Module.finrank ℚ (mulMap f g a b n hfa hgb hn).ker = D (n - a - b) := by
    rw [ker_mulMap_eq_range_koszulMap hf hfa hgb hcop hn]
    have hinj : Function.Injective (koszulMap f g a b n hfa hgb hn) := by
      intro p q hpq
      have h2 : (p : MvPolynomial (Fin 3) ℚ) * f = (q : MvPolynomial (Fin 3) ℚ) * f := by
        have := congrArg (fun z : H (n - a) × H (n - b) => (z.2 : MvPolynomial (Fin 3) ℚ)) hpq
        simpa [koszulMap] using this
      exact Subtype.ext (mul_right_cancel₀ hf h2)
    have h3 := LinearMap.finrank_range_add_finrank_ker (koszulMap f g a b n hfa hgb hn)
    rw [LinearMap.ker_eq_bot.mpr hinj, finrank_bot, add_zero] at h3
    rw [h3, finrank_H]
  have hD : Module.finrank ℚ (H (n - a) × H (n - b)) = D (n - a) + D (n - b) := by
    rw [Module.finrank_prod, finrank_H, finrank_H]
  rw [hD] at hB
  rw [hC] at hB
  rw [finrank_H] at hA
  have hmain : Module.finrank ℚ (H n ⧸ (mulMap f g a b n hfa hgb hn).range) = a * b := by
    have h1 : D n = Module.finrank ℚ (mulMap f g a b n hfa hgb hn).range + a * b := by
      have h := D_arith a b n hn
      rw [← hB] at h
      have h' : D n + D (n - a - b)
          = (Module.finrank ℚ (mulMap f g a b n hfa hgb hn).range + a * b)
            + D (n - a - b) := by
        rw [h]; ac_rfl
      exact add_right_cancel h'
    have h2 : Module.finrank ℚ (H n ⧸ (mulMap f g a b n hfa hgb hn).range) = a * b := by
      rw [h1] at hA
      exact add_right_cancel (hA.trans (Nat.add_comm
        (Module.finrank ℚ (mulMap f g a b n hfa hgb hn).range) (a * b)))
    exact h2
  rw [hmain]


/-! ## 6. Bézout: counting the common points -/

/-- The set of common rational points of `f` and `g`. -/
def Zset (f g : MvPolynomial (Fin 3) ℚ) : Set (Submodule ℚ (Fin 3 → ℚ)) :=
  {L | Module.finrank ℚ L = 1 ∧ ∀ x ∈ L, MvPolynomial.eval x f = 0 ∧ MvPolynomial.eval x g = 0}

/-- The evaluation map on forms of degree `n` at the points `x i`. -/
noncomputable def evalMap (n : ℕ) {N : ℕ} (x : Fin N → (Fin 3 → ℚ)) : H n →ₗ[ℚ] (Fin N → ℚ) where
  toFun h := fun i => MvPolynomial.eval (x i) (h : MvPolynomial (Fin 3) ℚ)
  map_add' h h' := by ext i; simp only [Pi.add_apply, Submodule.coe_add, map_add]
  map_smul' c h := by
    ext i
    simp only [Pi.smul_apply, Submodule.coe_smul, smul_eq_C_mul, map_mul, MvPolynomial.eval_C,
      smul_eq_mul, RingHom.id_apply]

@[simp]
lemma evalMap_apply (n : ℕ) {N : ℕ} (x : Fin N → (Fin 3 → ℚ)) (h : H n) (i : Fin N) :
    evalMap n x h i = MvPolynomial.eval (x i) (h : MvPolynomial (Fin 3) ℚ) := rfl

/-- **Bézout's bound** for coprime homogeneous forms of degrees `a`, `b`. -/
lemma bezout_fin {f g : MvPolynomial (Fin 3) ℚ} {a b N : ℕ} (hf : f ≠ 0) (hg : g ≠ 0)
    (hfa : f.IsHomogeneous a) (hgb : g.IsHomogeneous b)
    (hcop : ∀ h, h ∣ f → h ∣ g → IsUnit h)
    (x : Fin N → (Fin 3 → ℚ)) (hxne : ∀ i, x i ≠ 0)
    (hxind : ∀ i j, i ≠ j → ∀ c : ℚ, x j ≠ c • x i)
    (hf0 : ∀ i, MvPolynomial.eval (x i) f = 0) (hg0 : ∀ i, MvPolynomial.eval (x i) g = 0) :
    N ≤ a * b := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · omega
  set n := max (a + b) (N - 1) with hn
  have hn1 : a + b ≤ n := le_max_left _ _
  have hn2 : N - 1 ≤ n := le_max_right _ _
  have hsurj : Function.Surjective (evalMap n x) := by
    intro c
    obtain ⟨h, hh, hhe⟩ := homogeneousInterpolation x hxne hxind hn2 c
    exact ⟨⟨h, hh⟩, by ext i; exact hhe i⟩
  have hker : (mulMap f g a b n hfa hgb hn1).range ≤ (evalMap n x).ker := by
    rintro y ⟨z, rfl⟩
    rw [LinearMap.mem_ker]
    ext i
    simp only [evalMap_apply]
    have hy : ((mulMap f g a b n hfa hgb hn1 z : H n) : MvPolynomial (Fin 3) ℚ)
        = (z.1 : MvPolynomial (Fin 3) ℚ) * f + (z.2 : MvPolynomial (Fin 3) ℚ) * g := rfl
    rw [hy, map_add, map_mul, map_mul, hf0 i, hg0 i, mul_zero, mul_zero, add_zero,
      Pi.zero_apply]
  have hcodim := finrank_quot_mulMap_le (a := a) (b := b) (n := n) hf hfa hgb hcop hn1
  have hmono : Module.finrank ℚ (H n ⧸ (evalMap n x).ker)
      ≤ Module.finrank ℚ (H n ⧸ (mulMap f g a b n hfa hgb hn1).range) := by
    have h1 := Submodule.finrank_quotient_add_finrank ((evalMap n x).ker)
    have h2 := Submodule.finrank_quotient_add_finrank ((mulMap f g a b n hfa hgb hn1).range)
    have h3 : Module.finrank ℚ ((mulMap f g a b n hfa hgb hn1).range)
        ≤ Module.finrank ℚ ((evalMap n x).ker) := Submodule.finrank_mono hker
    omega
  have hq : Module.finrank ℚ (H n ⧸ (evalMap n x).ker) = N := by
    have hrange : (evalMap n x).range = ⊤ := LinearMap.range_eq_top.mpr hsurj
    have h1 := LinearMap.finrank_range_add_finrank_ker (evalMap n x)
    rw [hrange, finrank_top] at h1
    have h2 := Submodule.finrank_quotient_add_finrank ((evalMap n x).ker)
    have h4 : Module.finrank ℚ (Fin N → ℚ) = N := by simp
    omega
  omega

lemma eq_of_mem_of_finrank_eq_one {L L' : Submodule ℚ (Fin 3 → ℚ)}
    (hL : Module.finrank ℚ L = 1) (hL' : Module.finrank ℚ L' = 1) {v : Fin 3 → ℚ} (hv : v ≠ 0)
    (hvL : v ∈ L) (hvL' : v ∈ L') : L = L' := by
  have h1 : Submodule.span ℚ {v} ≤ L := Submodule.span_le.mpr (by simpa using hvL)
  have h2 : Module.finrank ℚ (Submodule.span ℚ {v}) = 1 := finrank_span_singleton hv
  have h3 : Submodule.span ℚ {v} = L := Submodule.eq_of_le_of_finrank_eq h1 (by rw [h2, hL])
  have h4 : Submodule.span ℚ {v} ≤ L' := Submodule.span_le.mpr (by simpa using hvL')
  have h5 : Submodule.span ℚ {v} = L' := Submodule.eq_of_le_of_finrank_eq h4 (by rw [h2, hL'])
  rw [← h3, h5]

theorem bezout {f g : MvPolynomial (Fin 3) ℚ} {a b : ℕ} (hf : f ≠ 0) (hg : g ≠ 0)
    (hfa : f.IsHomogeneous a) (hgb : g.IsHomogeneous b)
    (hcop : ∀ h, h ∣ f → h ∣ g → IsUnit h) :
    (Zset f g).Finite ∧ (Zset f g).ncard ≤ a * b := by
  classical
  have key : ∀ t : Finset (Submodule ℚ (Fin 3 → ℚ)), (∀ L ∈ t, L ∈ Zset f g) → t.card ≤ a * b := by
    intro t ht
    have hne : ∀ L : ↥t, ((L : ↥t) : Submodule ℚ (Fin 3 → ℚ)) ≠ ⊥ := by
      intro L hbot
      have h1 : Module.finrank ℚ (((L : ↥t) : Submodule ℚ (Fin 3 → ℚ))) = 1 := (ht L L.2).1
      rw [hbot, finrank_bot ℚ (Fin 3 → ℚ)] at h1
      exact absurd h1 (by norm_num)
    let xs : ↥t → (Fin 3 → ℚ) :=
      fun L => Classical.choose (Submodule.exists_mem_ne_zero_of_ne_bot (hne L))
    have hxs_mem : ∀ L : ↥t, xs L ∈ ((L : ↥t) : Submodule ℚ (Fin 3 → ℚ)) := fun L =>
      (Classical.choose_spec (Submodule.exists_mem_ne_zero_of_ne_bot (hne L))).1
    have hxs_ne : ∀ L : ↥t, xs L ≠ 0 := fun L =>
      (Classical.choose_spec (Submodule.exists_mem_ne_zero_of_ne_bot (hne L))).2
    let e : ↥t ≃ Fin (Fintype.card ↥t) := Fintype.equivFin ↥t
    let x : Fin (Fintype.card ↥t) → (Fin 3 → ℚ) := fun i => xs (e.symm i)
    have hxne : ∀ i, x i ≠ 0 := fun i => hxs_ne (e.symm i)
    have hxind : ∀ i j, i ≠ j → ∀ c : ℚ, x j ≠ c • x i := by
      intro i j hij c hc
      have hmem : x j ∈ ((e.symm i : ↥t) : Submodule ℚ (Fin 3 → ℚ)) := by
        rw [hc]
        exact Submodule.smul_mem _ c (hxs_mem (e.symm i))
      have heq : ((e.symm j : ↥t) : Submodule ℚ (Fin 3 → ℚ))
          = ((e.symm i : ↥t) : Submodule ℚ (Fin 3 → ℚ)) :=
        eq_of_mem_of_finrank_eq_one (ht _ (e.symm j).2).1 (ht _ (e.symm i).2).1
          (hxs_ne (e.symm j)) (hxs_mem (e.symm j)) hmem
      exact hij (e.symm.injective (Subtype.ext heq.symm))
    have hf0 : ∀ i, MvPolynomial.eval (x i) f = 0 :=
      fun i => ((ht _ (e.symm i).2).2 _ (hxs_mem (e.symm i))).1
    have hg0 : ∀ i, MvPolynomial.eval (x i) g = 0 :=
      fun i => ((ht _ (e.symm i).2).2 _ (hxs_mem (e.symm i))).2
    have h := bezout_fin hf hg hfa hgb hcop x hxne hxind hf0 hg0
    rw [Fintype.card_coe] at h
    exact h
  have hfin : (Zset f g).Finite := by
    by_contra hcon
    obtain ⟨t, ht, hcard⟩ := Set.Infinite.exists_subset_card_eq hcon (a * b + 1)
    have := key t (fun L hL => ht hL)
    omega
  refine ⟨hfin, ?_⟩
  rw [Set.ncard_eq_toFinset_card (Zset f g) hfin]
  exact key _ (fun L hL => hfin.mem_toFinset.mp hL)


/-! ## 7. The plane bound -/

lemma degree_eq_support_sum (s : Fin 3 →₀ ℕ) : s.degree = ∑ n ∈ s.support, s n := by
  rw [Finsupp.degree_eq_weight_one, Finsupp.weight_apply, Finsupp.sum]
  simp

lemma eval_smul_monomial (c : ℚ) (x : Fin 3 → ℚ) (s : Fin 3 →₀ ℕ) (a : ℚ) :
    MvPolynomial.eval (c • x) (MvPolynomial.monomial s a)
      = c ^ s.degree * MvPolynomial.eval x (MvPolynomial.monomial s a) := by
  rw [MvPolynomial.eval_monomial, MvPolynomial.eval_monomial, degree_eq_support_sum]
  rw [Finsupp.prod, Finsupp.prod,
    Finset.prod_congr rfl (fun n _ => by rw [Pi.smul_apply, smul_eq_mul, mul_pow]),
    Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  ring

lemma eval_smul {q : MvPolynomial (Fin 3) ℚ} {e : ℕ} (hq : q.IsHomogeneous e) (c : ℚ)
    (x : Fin 3 → ℚ) : MvPolynomial.eval (c • x) q = c ^ e * MvPolynomial.eval x q := by
  have h1 : MvPolynomial.eval x q
      = ∑ s ∈ q.support, MvPolynomial.eval x (MvPolynomial.monomial s (q.coeff s)) := by
    conv_lhs => rw [MvPolynomial.as_sum q]
    rw [map_sum]
  have h2 : MvPolynomial.eval (c • x) q
      = ∑ s ∈ q.support, MvPolynomial.eval (c • x) (MvPolynomial.monomial s (q.coeff s)) := by
    conv_lhs => rw [MvPolynomial.as_sum q]
    rw [map_sum]
  rw [h2, h1, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [eval_smul_monomial]
  have hdeg : s.degree = e := by
    rw [Finsupp.degree_eq_weight_one]
    exact hq (MvPolynomial.mem_support_iff.mp hs)
  rw [hdeg]

lemma exists_eq_C_of_isUnit {p : MvPolynomial (Fin 3) ℚ} (h : IsUnit p) :
    ∃ c : ℚ, p = MvPolynomial.C c := by
  obtain ⟨u, hu⟩ := h
  have h1 : (↑u : MvPolynomial (Fin 3) ℚ) * (↑u⁻¹ : MvPolynomial (Fin 3) ℚ) = 1 := u.mul_inv
  have h2 : (↑u : MvPolynomial (Fin 3) ℚ).totalDegree
      + (↑u⁻¹ : MvPolynomial (Fin 3) ℚ).totalDegree = 0 := by
    rw [← MvPolynomial.totalDegree_mul_of_isDomain u.ne_zero (u⁻¹).ne_zero, h1]
    simp
  have h3 : (↑u : MvPolynomial (Fin 3) ℚ).totalDegree = 0 := by omega
  exact ⟨_, by rw [← hu, MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp h3]⟩

lemma isUnit_C_of_ne_zero {c : ℚ} (hc : c ≠ 0) :
    IsUnit (MvPolynomial.C c : MvPolynomial (Fin 3) ℚ) :=
  ⟨⟨MvPolynomial.C c, MvPolynomial.C c⁻¹,
      by rw [← map_mul, mul_inv_cancel₀ hc, map_one],
      by rw [← map_mul, inv_mul_cancel₀ hc, map_one]⟩, rfl⟩

lemma mem_span_singleton_of_finrank_eq_one {L : Submodule ℚ (Fin 3 → ℚ)}
    (hL : Module.finrank ℚ L = 1) {y : Fin 3 → ℚ} (hy : y ∈ L) (hyne : y ≠ 0) {x : Fin 3 → ℚ}
    (hx : x ∈ L) : ∃ c : ℚ, x = c • y := by
  have h1 : Submodule.span ℚ {y} ≤ L := Submodule.span_le.mpr (by simpa using hy)
  have h2 : Module.finrank ℚ (Submodule.span ℚ {y}) = 1 := finrank_span_singleton hyne
  have h3 : Submodule.span ℚ {y} = L := Submodule.eq_of_le_of_finrank_eq h1 (by rw [h2, hL])
  have h4 : x ∈ Submodule.span ℚ {y} := by rw [h3]; exact hx
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp h4
  exact ⟨c, hc.symm⟩

theorem planeBound :
    ∃ B : ℕ, ∀ (n : ℕ) (G : Fin n → MvPolynomial (Fin 3) ℚ),
      (∀ i, G i ≠ 0) →
      (∀ i, ∃ d : ℕ, d ≤ 4 ∧ (G i).IsHomogeneous d) →
      (∀ h : MvPolynomial (Fin 3) ℚ, (∀ i, h ∣ G i) → IsUnit h) →
      {L : Submodule ℚ (Fin 3 → ℚ) | Module.finrank ℚ L = 1 ∧
        ∀ x ∈ L, ∀ i, MvPolynomial.eval x (G i) = 0}.Finite ∧
      {L : Submodule ℚ (Fin 3 → ℚ) | Module.finrank ℚ L = 1 ∧
        ∀ x ∈ L, ∀ i, MvPolynomial.eval x (G i) = 0}.ncard ≤ B := by
  classical
  refine ⟨16, ?_⟩
  intro n G hne hhom hcop
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    exact absurd (hcop 0 (fun i => i.elim0)) not_isUnit_zero
  · haveI : NeZero n := ⟨by omega⟩
    set Z : Set (Submodule ℚ (Fin 3 → ℚ)) :=
      {L | Module.finrank ℚ L = 1 ∧ ∀ x ∈ L, ∀ i, MvPolynomial.eval x (G i) = 0} with hZ
    have key_finrank : ∀ L : Submodule ℚ (Fin 3 → ℚ), Module.finrank ℚ L = 1 → L ≠ ⊥ := by
      intro L hL hbot
      rw [hbot, finrank_bot ℚ (Fin 3 → ℚ)] at hL
      exact absurd hL (by norm_num)
    by_cases hunit : IsUnit (G 0)
    · have hZempty : Z ⊆ ∅ := by
        intro L hL
        obtain ⟨y, hy, hyne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (key_finrank L hL.1)
        obtain ⟨c, hc⟩ := exists_eq_C_of_isUnit hunit
        have h0 := hL.2 y hy 0
        have hc0 : c ≠ 0 := by
          intro hc0
          exact hne 0 (by rw [hc, hc0, map_zero])
        rw [hc, MvPolynomial.eval_C] at h0
        exact hc0 h0
      rw [hZ]
      exact ⟨Set.finite_empty.subset hZempty,
        (Set.ncard_le_ncard hZempty Set.finite_empty).trans (by simp)⟩
    · obtain ⟨d₀, hd₀le, hd₀hom⟩ := hhom 0
      have hd₀pos : 1 ≤ d₀ := by
        rcases Nat.eq_zero_or_pos d₀ with h0 | h0
        · exfalso
          have htd : (G 0).totalDegree = 0 := by rw [hd₀hom.totalDegree (hne 0), h0]
          have hCG := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp htd
          have hc0 : (G 0).coeff 0 ≠ 0 := by
            intro hc
            exact hne 0 (by rw [hCG, hc, map_zero])
          rw [hCG] at hunit
          exact hunit (isUnit_C_of_ne_zero hc0)
        · exact h0
      obtain ⟨q, e, hqhom, hqsum, hqiff, hqirr⟩ :=
        factorizationHomogeneous (G := G 0) (hne 0) hd₀hom
      have hex : ∀ s : Fin d₀, e s ≠ 0 → ∃ i : Fin n, ¬ (q s ∣ G i) := by
        intro s hes
        rcases hqirr s with ⟨h1, h2⟩ | ⟨hirr, he1⟩
        · exact absurd h2 hes
        · by_contra hcon
          push_neg at hcon
          exact hirr.not_isUnit (hcop (q s) hcon)
      set is : Fin d₀ → Fin n := fun s => if h : e s = 0 then (0 : Fin n) else Classical.choose (hex s h)
        with his
      have his_eq : ∀ s (h : e s ≠ 0), is s = Classical.choose (hex s h) := by
        intro s h
        simp only [is, dif_neg h]
      have hcops : ∀ s, e s ≠ 0 → ∀ h : MvPolynomial (Fin 3) ℚ, h ∣ q s → h ∣ G (is s) → IsUnit h := by
        intro s hes h h1 h2
        rcases hqirr s with ⟨hq1, he0⟩ | ⟨hirr, he1⟩
        · exact absurd he0 hes
        · obtain ⟨t, ht⟩ := h1
          rcases hirr.isUnit_or_isUnit ht with hu | hu
          · exact hu
          · obtain ⟨v, hv⟩ := hu
            have hdiv : q s ∣ h := by
              refine ⟨↑v⁻¹, ?_⟩
              rw [ht, ← hv, mul_assoc, Units.mul_inv, mul_one]
            have hnot : ¬ (q s ∣ G (is s)) := by
              rw [his_eq s hes]
              exact Classical.choose_spec (hex s hes)
            exact absurd (hdiv.trans h2) hnot
      set Zs : Fin d₀ → Set (Submodule ℚ (Fin 3 → ℚ)) := fun s => Zset (q s) (G (is s)) with hZs
      have hempty : ∀ s, e s = 0 → Zs s ⊆ ∅ := by
        intro s hes L hL
        rcases hqirr s with ⟨hq1, -⟩ | ⟨-, he1⟩
        · obtain ⟨y, hy, hyne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (key_finrank L hL.1)
          have h0 := (hL.2 y hy).1
          rw [hq1, map_one] at h0
          exact one_ne_zero h0
        · exact absurd he1 (by omega)
      have hZsfin : ∀ s, (Zs s).Finite := by
        intro s
        by_cases hes : e s = 0
        · exact Set.finite_empty.subset (hempty s hes)
        · rcases hqirr s with ⟨h1, h2⟩ | ⟨hirr, he1⟩
          · exact absurd h2 hes
          · obtain ⟨b, hble, hbhom⟩ := hhom (is s)
            exact (bezout hirr.ne_zero (hne (is s)) (hqhom s) hbhom (hcops s hes)).1
      have hZsbd : ∀ s, (Zs s).ncard ≤ e s * 4 := by
        intro s
        by_cases hes : e s = 0
        · rw [hes]
          exact (Set.ncard_le_ncard (hempty s hes) Set.finite_empty).trans (by simp)
        · rcases hqirr s with ⟨h1, h2⟩ | ⟨hirr, he1⟩
          · exact absurd h2 hes
          · obtain ⟨b, hble, hbhom⟩ := hhom (is s)
            calc (Zs s).ncard ≤ e s * b :=
                  (bezout hirr.ne_zero (hne (is s)) (hqhom s) hbhom (hcops s hes)).2
              _ ≤ e s * 4 := Nat.mul_le_mul_left _ hble
      have hsub : Z ⊆ ⋃ s ∈ (Finset.univ : Finset (Fin d₀)), Zs s := by
        intro L hL
        obtain ⟨y, hy, hyne⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (key_finrank L hL.1)
        have h0 := hL.2 y hy 0
        rw [hqiff y] at h0
        obtain ⟨s, hs⟩ := h0
        refine Set.mem_biUnion (Finset.mem_univ s) ?_
        refine ⟨hL.1, fun x' hx' => ⟨?_, hL.2 x' hx' (is s)⟩⟩
        obtain ⟨c, hc⟩ := mem_span_singleton_of_finrank_eq_one hL.1 hy hyne hx'
        rw [hc]
        rcases hqirr s with ⟨hq1, -⟩ | ⟨hirr, he1⟩
        · rw [hq1, map_one] at hs
          exact absurd hs one_ne_zero
        · rw [eval_smul (hqhom s), hs, mul_zero]
      have hcard : (⋃ s ∈ (Finset.univ : Finset (Fin d₀)), Zs s).ncard
          ≤ ∑ s : Fin d₀, (Zs s).ncard := by
        induction (Finset.univ : Finset (Fin d₀)) using Finset.induction with
        | empty => simp
        | insert a s ha ih =>
          rw [Finset.set_biUnion_insert, Finset.sum_insert ha]
          exact (Set.ncard_union_le _ _).trans (add_le_add_right ih ((Zs a).ncard))
      have hsum : ∑ s : Fin d₀, (Zs s).ncard ≤ 16 := by
        calc ∑ s : Fin d₀, (Zs s).ncard ≤ ∑ s : Fin d₀, e s * 4 :=
              Finset.sum_le_sum fun s _ => hZsbd s
          _ = 4 * ∑ s : Fin d₀, e s := by rw [← Finset.sum_mul, mul_comm]
          _ = 4 * d₀ := by rw [hqsum]
          _ ≤ 4 * 4 := Nat.mul_le_mul_left _ hd₀le
          _ = 16 := by norm_num
      have hfinU : (⋃ s ∈ (Finset.univ : Finset (Fin d₀)), Zs s).Finite :=
        Set.Finite.biUnion (Finset.finite_toSet _) (fun s _ => hZsfin s)
      rw [hZ]
      refine ⟨hfinU.subset hsub, ?_⟩
      calc Z.ncard ≤ (⋃ s ∈ (Finset.univ : Finset (Fin d₀)), Zs s).ncard :=
            Set.ncard_le_ncard hsub hfinU
        _ ≤ ∑ s : Fin d₀, (Zs s).ncard := hcard
        _ ≤ 16 := hsum


end Work.Q44Geom
