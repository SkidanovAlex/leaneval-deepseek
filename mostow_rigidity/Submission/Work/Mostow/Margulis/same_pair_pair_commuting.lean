import Mathlib
import Submission.Work.Mostow.margulisPairDefs
import Submission.Work.Mostow.geomFiniteDefs
import Submission.Work.Mostow.pairStabCocycleDiscrete
import Submission.Work.Mostow.pairStabDefs

namespace Work.Mostow.Margulis

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory Matrix

set_option linter.style.haveILetI false

/-! ## Helper lemmas: a point on the axis of a pair of boundary points, and the
group-theoretic core of the Margulis lemma. -/

/-! ### The axis point of a pair `{ξ, η}` and Busemann translation length

For `g` fixing two distinct boundary points `ξ ≠ η`, the point `pairPoint ξ η` lies on the
geodesic joining them and `g` translates it by exactly the absolute value of its Busemann
translation length at `ξ`. -/

theorem hdist_pairPoint_eq_abs_busemann (n : ℕ) (hA : POActionProp n) (hI : HypIsometryProp n)
    (ξ η : E n) (hξ : ξ ∈ Sph n) (hη : η ∈ Sph n) (hne : ξ ≠ η) :
    ∀ g : PO n 1, bd g ξ = ξ → bd g η = η →
      hdist (pairPoint ξ η) (g • pairPoint ξ η) = |busemann ξ (g • (0 : E n))| := by
  intro g hgξ hgη
  obtain ⟨lam, hlam0, hlam⟩ := emat_eigen_of_bd g hξ hgξ
  obtain ⟨mu, hmu0, hmu⟩ := emat_eigen_of_bd g hη hgη
  have hprod : lam * mu = 1 := eigen_mul_eq_one g hξ hη hne hlam hmu
  obtain ⟨-, hlampos, hbus⟩ := lev_emat_eigen g hξ hlam
  have hp : hlift (pairPoint ξ η) = pairR ξ η • (theta ξ + theta η) := hlift_pairPoint ξ η hξ hη hne
  have hgp : hlift (g • pairPoint ξ η) = pairR ξ η • (lam • theta ξ + mu • theta η) := by
    rw [← emat_hlift g (pairPoint ξ η), hp, Matrix.mulVec_smul, Matrix.mulVec_add, hlam, hmu]
  have hic : inner ℝ η ξ = inner ℝ ξ η := (real_inner_comm η ξ).symm
  have hkey : mform (theta ξ + theta η) (lam • theta ξ + mu • theta η)
      = (lam + mu) * (inner ℝ ξ η - 1) := by
    simp only [mform_add_left, mform_add_right, mform_smul_left, mform_smul_right,
      mform_theta_theta_sph ξ hξ, mform_theta_theta_sph η hη, mform_theta_theta_pair, hic,
      mul_zero, zero_mul, zero_add, add_zero]
    ring
  have hpair : mform (hlift (pairPoint ξ η)) (hlift (g • pairPoint ξ η)) = -(lam + mu) / 2 := by
    rw [hp, hgp, mform_smul_left, mform_smul_right, hkey]
    have h2 : 0 < 2 * (1 - inner ℝ ξ η) := two_sub_inner_pos ξ η hξ hη hne
    have hR : pairR ξ η * pairR ξ η = (2 * (1 - inner ℝ ξ η))⁻¹ := pairR_mul_self ξ η h2
    have hne' : (2 * (1 - inner ℝ ξ η)) ≠ 0 := ne_of_gt h2
    have h1i : (1 - inner ℝ ξ η) ≠ 0 := by
      have hlt : inner ℝ ξ η < 1 :=
        inner_lt_one_of_ne_unit ((mem_Sph_iff ξ).1 hξ) ((mem_Sph_iff η).1 hη) hne
      linarith
    have hstep : (2 * (1 - inner ℝ ξ η))⁻¹ * (inner ℝ ξ η - 1) = -(1/2) := by
      field_simp
      ring
    calc pairR ξ η * (pairR ξ η * ((lam + mu) * (inner ℝ ξ η - 1)))
        = (pairR ξ η * pairR ξ η) * ((lam + mu) * (inner ℝ ξ η - 1)) := by ring
      _ = (2 * (1 - inner ℝ ξ η))⁻¹ * ((lam + mu) * (inner ℝ ξ η - 1)) := by rw [hR]
      _ = (lam + mu) * ((2 * (1 - inner ℝ ξ η))⁻¹ * (inner ℝ ξ η - 1)) := by ring
      _ = (lam + mu) * (-(1/2)) := by rw [hstep]
      _ = -(lam + mu) / 2 := by ring
  have hdist_eq : hdist (pairPoint ξ η) (g • pairPoint ξ η) = Real.arcosh ((lam + mu) / 2) := by
    rw [hdist, tpart_mul_sub_inner_eq_neg_mform, hpair]
    congr 1
    ring
  rw [hdist_eq, hbus, abs_neg]
  have hmu_eq : mu = lam⁻¹ := eq_inv_of_mul_eq_one_right hprod
  have hcosh : (lam + mu) / 2 = Real.cosh (Real.log lam) := by
    rw [hmu_eq, Real.cosh_eq, Real.exp_log hlampos, Real.exp_neg, Real.exp_log hlampos]
  rw [hcosh, ← Real.cosh_abs]
  exact Real.arcosh_cosh (abs_nonneg _)


/-! ### Group theory: finite kernel of a cocycle with values in `cℤ` -/

def gprod {G : Type*} [Group G] (f : ℕ → G) : ℕ → G
  | 0 => 1
  | (n + 1) => gprod f n * f n

@[simp] lemma gprod_zero {G : Type*} [Group G] (f : ℕ → G) : gprod f 0 = 1 := rfl
@[simp] lemma gprod_succ {G : Type*} [Group G] (f : ℕ → G) (n : ℕ) :
    gprod f (n + 1) = gprod f n * f n := rfl

lemma pow_mul_eq_gprod_conj {G : Type*} [Group G] (x y : G) (e : ℕ) :
    (x * y) ^ e = gprod (fun i => y ^ i * x * (y ^ i)⁻¹) e * y ^ e := by
  induction e with
  | zero => simp
  | succ n ih =>
      rw [gprod_succ, pow_succ, pow_succ, ih]
      group

lemma toAdd_eq_zero_iff (z : Multiplicative ℝ) : z.toAdd = 0 ↔ z = 1 := by
  constructor
  · intro h; simpa using h
  · intro h; rw [h]; rfl

lemma toAdd_mul' (p q : Multiplicative ℝ) : (p * q).toAdd = p.toAdd + q.toAdd := rfl
lemma toAdd_inv' (p : Multiplicative ℝ) : (p⁻¹).toAdd = -p.toAdd := rfl

lemma toAdd_pow_nat (x : Multiplicative ℝ) (n : ℕ) :
    (x ^ n).toAdd = (n : ℝ) * x.toAdd := by
  induction n with
  | zero => simp
  | succ k ih => rw [pow_succ, toAdd_mul', ih]; push_cast; ring

lemma toAdd_zpow (x : Multiplicative ℝ) (m : ℤ) :
    (x ^ m).toAdd = (m : ℝ) * x.toAdd := by
  cases m with
  | ofNat n =>
      rw [show (x ^ Int.ofNat n) = x ^ (n : ℤ) from rfl, zpow_natCast, toAdd_pow_nat]
      norm_num
  | negSucc n =>
      rw [zpow_negSucc]
      show ((x ^ (n + 1))⁻¹).toAdd = _
      rw [toAdd_inv', toAdd_pow_nat]
      push_cast; ring

example {G : Type*} [Group G] (S : Subgroup G) (f : ℕ → G) (e : ℕ) (h : ∀ i, f i ∈ S) :
    gprod f e ∈ S := by
  induction e with
  | zero => simp
  | succ n ih => rw [gprod_succ]; exact S.mul_mem ih (h n)

example {G : Type*} [Group G] (S : Subgroup G) (f : ℕ → G) (e : ℕ) (h : ∀ i, f i ∈ S) :
    gprod f e ∈ S := by
  induction e with
  | zero => simp
  | succ n ih => rw [gprod_succ]; exact mul_mem ih (h n)

theorem exists_pow_pow_commute_of_kernel_finite {G : Type*} [Group G] (S : Subgroup G)
    (φ : S →* Multiplicative ℝ) (c : ℝ)
    (hval : ∀ s : S, ∃ m : ℤ, (φ s).toAdd = m * c)
    (hker : (φ.ker : Set S).Finite)
    (a b : S) (ha : φ a ≠ 1) (hb : φ b ≠ 1) :
    ∃ m k : ℕ, 0 < m ∧ 0 < k ∧ (a : G) ^ m * (b : G) ^ k = (b : G) ^ k * (a : G) ^ m := by
  classical
  haveI hFinKer : Finite ↥φ.ker := hker.to_subtype
  haveI hFintKer : Fintype ↥φ.ker := Fintype.ofFinite _
  set N : ℕ := Nat.card ↥φ.ker with hN
  set e : ℕ := Nat.card (Equiv.Perm ↥φ.ker) with he
  have hNpos : 0 < N := by
    rw [hN, Nat.card_eq_fintype_card]
    exact Fintype.card_pos_iff.mpr ⟨⟨1, (φ.ker).one_mem⟩⟩
  have hepos : 0 < e := by
    rw [he, Nat.card_eq_fintype_card]
    exact Fintype.card_pos_iff.mpr ⟨1⟩
  have hnorm : (φ.ker).Normal := MonoidHom.normal_ker φ
  obtain ⟨a0, ha0⟩ := hval a
  obtain ⟨b0, hb0⟩ := hval b
  have ha0ne : a0 ≠ 0 := by
    intro h0
    exact ha ((toAdd_eq_zero_iff (φ a)).mp (by rw [ha0, h0]; norm_num))
  have hb0ne : b0 ≠ 0 := by
    intro h0
    exact hb ((toAdd_eq_zero_iff (φ b)).mp (by rw [hb0, h0]; norm_num))
  -- Bezout
  set g : ℤ := ((Int.gcd a0 b0 : ℕ) : ℤ) with hg
  obtain ⟨u, v, huv⟩ : ∃ u v : ℤ, u * a0 + v * b0 = g := by
    refine ⟨Int.gcdA a0 b0, Int.gcdB a0 b0, ?_⟩
    rw [mul_comm (Int.gcdA a0 b0) a0, mul_comm (Int.gcdB a0 b0) b0,
      ← Int.gcd_eq_gcd_ab a0 b0, hg]
  set h : S := a ^ u * b ^ v with hh
  have hhval : (φ h).toAdd = g * c := by
    rw [hh, map_mul, map_zpow, map_zpow, toAdd_mul', toAdd_zpow, toAdd_zpow, ha0, hb0]
    rw [← huv]; push_cast; ring
  have hhinvval : (φ h⁻¹).toAdd = -(g * c) := by
    rw [map_inv, toAdd_inv', hhval]
  -- the conjugation permutation of the kernel
  let ρ : Equiv.Perm ↥φ.ker :=
    { toFun := fun z => ⟨h * (z : S) * h⁻¹, hnorm.conj_mem (z : S) z.2 h⟩
      invFun := fun z => ⟨h⁻¹ * (z : S) * h, by
        simpa using hnorm.conj_mem (z : S) z.2 h⁻¹⟩
      left_inv := by intro z; ext; group
      right_inv := by intro z; ext; group }
  have ρ_apply : ∀ w : ↥φ.ker, (ρ w : S) = h * (w : S) * h⁻¹ := fun w => rfl
  have hρpow_el : ∀ n : ℕ, ∀ z : ↥φ.ker,
      (ρ ^ n) z = ⟨h ^ n * (z : S) * (h ^ n)⁻¹, hnorm.conj_mem _ z.2 _⟩ := by
    intro n
    induction n with
    | zero => intro z; ext; simp
    | succ m ih =>
        intro z
        have hstep : (ρ ^ (m + 1)) z = ρ ((ρ ^ m) z) := by rw [pow_succ', Equiv.Perm.mul_apply]
        rw [hstep, ih z]
        ext
        rw [ρ_apply, Subtype.coe_mk, pow_succ]
        group
  have hρpow : ∀ n : ℕ, ∀ z : ↥φ.ker, ((ρ ^ n) z : S) = h ^ n * (z : S) * (h ^ n)⁻¹ :=
    fun n z => congrArg Subtype.val (hρpow_el n z)
  have hcent_h : ∀ z : S, z ∈ φ.ker → h ^ e * z * (h ^ e)⁻¹ = z := by
    intro z hz
    have h1 : (ρ ^ e) ⟨z, hz⟩ = ⟨z, hz⟩ := by
      rw [he, Nat.card_eq_fintype_card, pow_card_eq_one]
      rfl
    have h2 := congrArg (fun t : ↥φ.ker => (t : S)) h1
    simpa only [hρpow e ⟨z, hz⟩] using h2
  have hcent_hinv : ∀ z : S, z ∈ φ.ker → (h⁻¹) ^ e * z * ((h⁻¹) ^ e)⁻¹ = z := by
    intro z hz
    have h1 : h ^ e * z = z * h ^ e := by
      have hx := hcent_h z hz
      have h2 := congrArg (fun t => t * h ^ e) hx
      simpa only [mul_assoc, inv_mul_cancel, mul_one] using h2
    have h2 : Commute ((h ^ e)⁻¹) z := Commute.inv_left (show Commute (h ^ e) z from h1)
    have h3 : (h ^ e)⁻¹ * z * h ^ e = z := by
      rw [h2.eq]
      group
    rw [inv_pow, inv_inv]
    exact h3
  -- the main step
  have key : ∀ (x y : S) (k : ℕ), (φ x).toAdd = (k : ℝ) * (φ y).toAdd →
      (∀ z : S, z ∈ φ.ker → y ^ e * z * (y ^ e)⁻¹ = z) →
      x ^ (e * N) = y ^ (k * (e * N)) := by
    intro x y k hxy hcent
    have hz : x * (y ^ k)⁻¹ ∈ φ.ker := by
      rw [MonoidHom.mem_ker, ← toAdd_eq_zero_iff, map_mul, map_inv, map_pow,
        toAdd_mul', toAdd_inv', toAdd_pow_nat, hxy]
      ring
    have hexp : x ^ e = gprod (fun i => (y ^ k) ^ i * (x * (y ^ k)⁻¹) * ((y ^ k) ^ i)⁻¹) e
        * (y ^ k) ^ e := by
      conv_lhs => rw [show x = (x * (y ^ k)⁻¹) * y ^ k by group]
      rw [pow_mul_eq_gprod_conj]
    have hmem : ∀ i : ℕ, ((y ^ k) ^ i * (x * (y ^ k)⁻¹) * ((y ^ k) ^ i)⁻¹) ∈ φ.ker :=
      fun i => hnorm.conj_mem _ hz _
    have hw : gprod (fun i => (y ^ k) ^ i * (x * (y ^ k)⁻¹) * ((y ^ k) ^ i)⁻¹) e ∈ φ.ker := by
      induction e with
      | zero => simp
      | succ n ih => rw [gprod_succ]; exact mul_mem ih (hmem n)
    have hcw : Commute (gprod (fun i => (y ^ k) ^ i * (x * (y ^ k)⁻¹) * ((y ^ k) ^ i)⁻¹) e : S)
        ((y ^ k) ^ e : S) := by
      have hc1 : Commute ((y : S) ^ e)
          (gprod (fun i => (y ^ k) ^ i * (x * (y ^ k)⁻¹) * ((y ^ k) ^ i)⁻¹) e : S) := by
        rw [commute_iff_eq]
        have h1 := hcent _ hw
        have h2 := congrArg (fun t => t * y ^ e) h1
        simpa only [mul_assoc, inv_mul_cancel, mul_one] using h2
      have hc2 : ((y ^ e) ^ k) = (y ^ k) ^ e := by rw [← pow_mul, ← pow_mul, mul_comm]
      have hc3 : Commute ((y ^ e) ^ k)
          (gprod (fun i => (y ^ k) ^ i * (x * (y ^ k)⁻¹) * ((y ^ k) ^ i)⁻¹) e) :=
        hc1.pow_left k
      rw [hc2] at hc3
      exact hc3.symm
    have hwN : (gprod (fun i => (y ^ k) ^ i * (x * (y ^ k)⁻¹) * ((y ^ k) ^ i)⁻¹) e) ^ N = 1 := by
      have h1 : (⟨gprod (fun i => (y ^ k) ^ i * (x * (y ^ k)⁻¹) * ((y ^ k) ^ i)⁻¹) e,
          hw⟩ : ↥φ.ker) ^ N = 1 := by
        rw [hN, Nat.card_eq_fintype_card, pow_card_eq_one]
      simpa using Subtype.ext_iff.mp h1
    calc x ^ (e * N) = (x ^ e) ^ N := pow_mul x e N
      _ = (gprod (fun i => (y ^ k) ^ i * (x * (y ^ k)⁻¹) * ((y ^ k) ^ i)⁻¹) e * (y ^ k) ^ e) ^ N := by
            rw [hexp]
      _ = (gprod (fun i => (y ^ k) ^ i * (x * (y ^ k)⁻¹) * ((y ^ k) ^ i)⁻¹) e) ^ N
            * ((y ^ k) ^ e) ^ N := hcw.mul_pow N
      _ = ((y ^ k) ^ e) ^ N := by rw [hwN, one_mul]
      _ = y ^ (k * (e * N)) := by rw [← pow_mul, ← pow_mul]
  -- orientations
  have natAbs_cast_of_nonneg : ∀ {m : ℤ}, 0 ≤ m → ((m.natAbs : ℕ) : ℝ) = (m : ℝ) := by
    intro m h
    have h1 : ((m.natAbs : ℤ) : ℝ) = (m : ℝ) := by rw [Int.natAbs_of_nonneg h]
    simpa using h1
  have ha_or : ∃ (y : S) (k : ℕ), (y = h ∨ y = h⁻¹) ∧ (φ a).toAdd = (k : ℝ) * (φ y).toAdd := by
    have hg_dvd : g ∣ a0 := by rw [hg]; exact Int.gcd_dvd_left a0 b0
    have hna : a0 / g * g = a0 := Int.ediv_mul_cancel hg_dvd
    have haval : (φ a).toAdd = ((a0 / g : ℤ) : ℝ) * (g * c) := by
      conv_lhs => rw [ha0, show a0 = a0 / g * g from hna.symm]
      push_cast; ring
    by_cases hpos : 0 ≤ (a0 / g)
    · refine ⟨h, (a0 / g).natAbs, Or.inl rfl, ?_⟩
      rw [haval, hhval, natAbs_cast_of_nonneg hpos] <;> ring
    · have hneg : (a0 / g) < 0 := not_le.mp hpos
      refine ⟨h⁻¹, (-(a0 / g)).natAbs, Or.inr rfl, ?_⟩
      rw [haval, hhinvval, natAbs_cast_of_nonneg (by linarith : (0:ℤ) ≤ -(a0 / g))]
      push_cast; ring
  have hb_or : ∃ (y : S) (k : ℕ), (y = h ∨ y = h⁻¹) ∧ (φ b).toAdd = (k : ℝ) * (φ y).toAdd := by
    have hg_dvd : g ∣ b0 := by rw [hg]; exact Int.gcd_dvd_right a0 b0
    have hnb : b0 / g * g = b0 := Int.ediv_mul_cancel hg_dvd
    have hbval : (φ b).toAdd = ((b0 / g : ℤ) : ℝ) * (g * c) := by
      conv_lhs => rw [hb0, show b0 = b0 / g * g from hnb.symm]
      push_cast; ring
    by_cases hpos : 0 ≤ (b0 / g)
    · refine ⟨h, (b0 / g).natAbs, Or.inl rfl, ?_⟩
      rw [hbval, hhval, natAbs_cast_of_nonneg hpos] <;> ring
    · have hneg : (b0 / g) < 0 := not_le.mp hpos
      refine ⟨h⁻¹, (-(b0 / g)).natAbs, Or.inr rfl, ?_⟩
      rw [hbval, hhinvval, natAbs_cast_of_nonneg (by linarith : (0:ℤ) ≤ -(b0 / g))]
      push_cast; ring
  obtain ⟨ya, ka, hya, hka⟩ := ha_or
  obtain ⟨yb, kb, hyb, hkb⟩ := hb_or
  have hcent_ya : ∀ z : S, z ∈ φ.ker → ya ^ e * z * (ya ^ e)⁻¹ = z := by
    rcases hya with rfl | rfl
    · exact hcent_h
    · exact hcent_hinv
  have hcent_yb : ∀ z : S, z ∈ φ.ker → yb ^ e * z * (yb ^ e)⁻¹ = z := by
    rcases hyb with rfl | rfl
    · exact hcent_h
    · exact hcent_hinv
  have hA : a ^ (e * N) = ya ^ (ka * (e * N)) := key a ya ka hka hcent_ya
  have hB : b ^ (e * N) = yb ^ (kb * (e * N)) := key b yb kb hkb hcent_yb
  have hzz : ∀ i j : ℤ, h ^ i * h ^ j = h ^ j * h ^ i := by
    intro i j
    rw [← _root_.zpow_add, ← _root_.zpow_add, add_comm]
  have hA' : ∃ z : ℤ, a ^ (e * N) = h ^ z := by
    rcases hya with rfl | rfl
    · exact ⟨_, by rw [hA, ← zpow_natCast]⟩
    · exact ⟨-((ka * (e * N) : ℕ) : ℤ), by rw [hA, inv_pow, ← zpow_natCast, ← _root_.zpow_neg]⟩
  have hB' : ∃ z : ℤ, b ^ (e * N) = h ^ z := by
    rcases hyb with rfl | rfl
    · exact ⟨_, by rw [hB, ← zpow_natCast]⟩
    · exact ⟨-((kb * (e * N) : ℕ) : ℤ), by rw [hB, inv_pow, ← zpow_natCast, ← _root_.zpow_neg]⟩
  obtain ⟨za, hza⟩ := hA'
  obtain ⟨zb, hzb⟩ := hB'
  refine ⟨e * N, e * N, Nat.mul_pos hepos hNpos, Nat.mul_pos hepos hNpos, ?_⟩
  have hS : a ^ (e * N) * b ^ (e * N) = b ^ (e * N) * a ^ (e * N) := by
    rw [hza, hzb, hzz]
  have hG := congrArg (fun t : S => (t : G)) hS
  simpa only [Subgroup.coe_mul, Subgroup.coe_pow] using hG


/-- **Margulis lemma, loxodromic case**: two elements `γ δ` of a discrete subgroup `Γ ≤ PO(n,1)`
which are entrywise close to the identity (`NearId q`, `8 (n+1)^3 q ≤ 1/2`), which fix no point of
`ℍⁿ` (so not elliptic), and which have the *same* two boundary fixed points `ξ ≠ η` (so `bdFix`
is the pair `{ξ, η}` for both) have commuting positive powers. -/
theorem same_pair_pair_commuting (n : ℕ) (hn : 3 ≤ n) (hA : POActionProp n)
    (hI : HypIsometryProp n) (Γ : Subgroup (PO n 1)) (hdisc : IsDiscrete (SetLike.coe Γ))
    (γ δ : Γ) (q : ℝ) (hq : 0 < q) (hsmall : 8 * (msz n) ^ 3 * q ≤ 1 / 2)
    (hγ : NearId q (γ : PO n 1)) (hδ : NearId q (δ : PO n 1))
    (hnfγ : ∀ u : E n, (γ : PO n 1) • u ≠ u) (hnfδ : ∀ u : E n, (δ : PO n 1) • u ≠ u)
    (ξ η : E n) (hξ : ξ ∈ Sph n) (hη : η ∈ Sph n) (hne : ξ ≠ η)
    (hγfix : bdFix (γ : PO n 1) = {ξ, η}) (hδfix : bdFix (δ : PO n 1) = {ξ, η}) :
    ∃ m k : ℕ, 0 < m ∧ 0 < k ∧
      (γ : PO n 1) ^ m * (δ : PO n 1) ^ k = (δ : PO n 1) ^ k * (γ : PO n 1) ^ m := by
  classical
  -- γ and δ each fix ξ and η
  have hγξ : bd (γ : PO n 1) ξ = ξ := by
    have hmem : ξ ∈ bdFix (γ : PO n 1) := by rw [hγfix]; simp
    rw [Work.Mostow.bdFix] at hmem
    exact hmem.2
  have hγη : bd (γ : PO n 1) η = η := by
    have hmem : η ∈ bdFix (γ : PO n 1) := by rw [hγfix]; simp
    rw [Work.Mostow.bdFix] at hmem
    exact hmem.2
  have hδξ : bd (δ : PO n 1) ξ = ξ := by
    have hmem : ξ ∈ bdFix (δ : PO n 1) := by rw [hδfix]; simp
    rw [Work.Mostow.bdFix] at hmem
    exact hmem.2
  have hδη : bd (δ : PO n 1) η = η := by
    have hmem : η ∈ bdFix (δ : PO n 1) := by rw [hδfix]; simp
    rw [Work.Mostow.bdFix] at hmem
    exact hmem.2
  -- the pair-stabiliser property
  have hpair : ∃ p : E n, ∀ g : PO n 1, bd g ξ = ξ → bd g η = η →
      hdist p (g • p) = |busemann ξ (g • (0 : E n))| :=
    ⟨Work.Mostow.pairPoint ξ η,
      hdist_pairPoint_eq_abs_busemann n hA hI ξ η hξ hη hne⟩
  obtain ⟨c, hval, hker⟩ :=
    Work.Mostow.pairStabCocycleDiscrete n (by omega) hA hI Γ hdisc ξ η hξ hη hne hpair
  -- the subgroup fixing ξ and η, and the Busemann cocycle on it
  let S : Subgroup Γ := Work.Mostow.pairStab hA Γ ξ η hξ hη
  let φ : S →* Multiplicative ℝ :=
    { toFun := fun s => Multiplicative.ofAdd (busemann ξ (((s : Γ) : PO n 1) • (0 : E n)))
      map_one' := by
        show Multiplicative.ofAdd (busemann ξ ((((1 : S) : Γ) : PO n 1) • (0 : E n))) = 1
        rw [show (((1 : S) : Γ) : PO n 1) = 1 from rfl, (POBasic.ofProp hA).one_smul,
          Work.Mostow.busemann_zero]
        rfl
      map_mul' := by
        intro s t
        show Multiplicative.ofAdd (busemann ξ ((((s * t : S) : Γ) : PO n 1) • (0 : E n)))
          = Multiplicative.ofAdd (busemann ξ ((((s : Γ) : PO n 1) • (0 : E n))))
            * Multiplicative.ofAdd (busemann ξ ((((t : Γ) : PO n 1) • (0 : E n))))
        rw [show (((s * t : S) : Γ) : PO n 1)
            = ((s : Γ) : PO n 1) * ((t : Γ) : PO n 1) from rfl]
        rw [Work.Mostow.busemann_stab_mul hA hI ξ hξ ((s : Γ) : PO n 1) ((t : Γ) : PO n 1)
          s.2.1]
        rfl }
  have hval' : ∀ s : S, ∃ m : ℤ, (φ s).toAdd = m * c := by
    intro s
    obtain ⟨m, hm⟩ := hval (s : Γ) s.2.1 s.2.2
    exact ⟨m, hm⟩
  have hker' : (φ.ker : Set S).Finite := by
    have hsub : ((fun s : S => (s : Γ)) '' (φ.ker : Set S))
        ⊆ {γ : Γ | bd (γ : PO n 1) ξ = ξ ∧ bd (γ : PO n 1) η = η ∧
            busemann ξ ((γ : PO n 1) • (0 : E n)) = 0} := by
      rintro _ ⟨s, hs, rfl⟩
      have hs' : φ s = 1 := MonoidHom.mem_ker.mp (SetLike.mem_coe.mp hs)
      exact ⟨s.2.1, s.2.2, (toAdd_eq_zero_iff (φ s)).mp (by rw [hs']; rfl)⟩
    refine (hker.subset hsub).of_finite_image ?_
    intro a _ b _ hab
    exact Subtype.ext hab
  -- γ and δ as elements of `S`
  have ha : φ ⟨γ, ⟨hγξ, hγη⟩⟩ ≠ 1 := by
    intro h1
    have hbus : busemann ξ ((γ : PO n 1) • (0 : E n)) = 0 := by
      have h0 : (φ ⟨γ, ⟨hγξ, hγη⟩⟩).toAdd = 0 := by rw [h1]; rfl
      exact h0
    have hfix : (γ : PO n 1) • Work.Mostow.pairPoint ξ η = Work.Mostow.pairPoint ξ η := by
      rw [← (HypIsoData.ofProp hI).eq_zero, (HypIsoData.ofProp hI).symm,
        hdist_pairPoint_eq_abs_busemann n hA hI ξ η hξ hη hne (γ : PO n 1) hγξ hγη, hbus,
        abs_zero]
    exact hnfγ (Work.Mostow.pairPoint ξ η) hfix
  have hb : φ ⟨δ, ⟨hδξ, hδη⟩⟩ ≠ 1 := by
    intro h1
    have hbus : busemann ξ ((δ : PO n 1) • (0 : E n)) = 0 := by
      have h0 : (φ ⟨δ, ⟨hδξ, hδη⟩⟩).toAdd = 0 := by rw [h1]; rfl
      exact h0
    have hfix : (δ : PO n 1) • Work.Mostow.pairPoint ξ η = Work.Mostow.pairPoint ξ η := by
      rw [← (HypIsoData.ofProp hI).eq_zero, (HypIsoData.ofProp hI).symm,
        hdist_pairPoint_eq_abs_busemann n hA hI ξ η hξ hη hne (δ : PO n 1) hδξ hδη, hbus,
        abs_zero]
    exact hnfδ (Work.Mostow.pairPoint ξ η) hfix
  obtain ⟨m, k, hm, hk, hcomm⟩ :=
    exists_pow_pow_commute_of_kernel_finite S φ c hval' hker'
      ⟨γ, ⟨hγξ, hγη⟩⟩ ⟨δ, ⟨hδξ, hδη⟩⟩ ha hb
  refine ⟨m, k, hm, hk, ?_⟩
  have hG := congrArg (fun t : Γ => ((t : PO n 1))) hcomm
  simpa only [Subgroup.coe_pow, Subgroup.coe_mul] using hG

end Work.Mostow.Margulis
