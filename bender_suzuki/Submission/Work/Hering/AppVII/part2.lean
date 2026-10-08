import Mathlib
import Submission.Work.PGroup.Basic
import Submission.Work.PGroup.center_eq_commutator_of_isExtraspecial
import Submission.Work.CharCore.Basic
import Submission.Work.CharCore.Main
import Submission.Work.Clifford.All
import Submission.Work.CharPrelim.extend_char_of_cyclic_quotient
import Submission.Work.Hering.AppVII.Extraspecial
import Submission.Work.Hering.AppVII.part2_central_scalar
import Submission.Work.Hering.AppVII.part2_coset_self
import Submission.Work.Hering.AppVII.part2_sum_bijection
import Submission.Work.Hering.AppVII.part2_final_step
import Submission.Work.Hering.AppVII.part2_quotient_cyclic
import Submission.Work.Hering.AppVII.part2_orbitSum_norm
import Submission.Work.Hering.AppVII.part2_count
import Submission.Work.Hering.AppVII.part2_res_eq_of_invariant

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Appendix VII (Peterfalvi I, pp. 216–220), Part 2: the character-theoretic heart

Let `H = Q ⋊ P` where `P` has prime order `p`, `p ∤ |Q|`, `Q` is extraspecial of order
`q ^ (2m+1)` with `q` odd, `[P,Q] = Q` and `C_Q(P) = Z(Q)`.  Then every irreducible character
`χ` of `H` whose kernel does not contain `Z(Q)` satisfies `1_P ⊆ Res_P χ`, equivalently
`∑_{s ∈ P} χ s ≠ 0`.

The proof follows the source (steps 3–6 of Part 2):

* Clifford's theorem gives `θ ∈ Irr Q` and `e > 0` with `Res_Q χ = e · (orbit sum of θ)`;
* if `θ` is `H`-invariant then `θ` extends to `H` (the quotient `H/Q ≅ P` is cyclic) and
  Gallagher's theorem forces `Res_Q χ = θ`, i.e. `e = 1`; otherwise the inertia subgroup is
  `Q` and the same conclusion `e = 1` follows from the count below;
* on each coset `Q s` (`s ∈ P^#`) the values `‖χ‖²` are constant, equal to `‖χ s‖²`: this is
  the fixed-point-free action of `P` on `Q/Z(Q)` (`Q` has class two, so `t s t⁻¹ = ⁅t,s⁆ s`);
* counting `∑_{y ∈ H} ‖χ y‖² = |H|` against `∑_{y ∈ Q} ‖χ y‖²` gives
  `∑_{s ∈ P^#} ‖χ s‖² = p - e²·(orbit size)`, whence `p ∑_i n_i² - (∑_i n_i)² = p - e²·(orbit size)`
  for the multiplicities `n_i` of the linear characters of `P` in `Res_P χ`;
* this forces `e = 1`; then the multiplicities `n_i` satisfy
  `∑_{i<j} (n_i - n_j)² = p - 1`, and the elementary arithmetic lemma together with
  `χ(1) = q^k` (a power of `q`, since `θ(1) ∣ |Q|`) and `χ(1) ≠ 1` shows that *every* `n_i`
  is nonzero.  Hence so is the multiplicity of the trivial character, i.e. `∑_{s ∈ P} χ s ≠ 0`.
-/

set_option maxHeartbeats 1000000

open scoped commutatorElement

noncomputable section

namespace Work.Hering.AppVII

open Classical

variable {H : Type*} [Group H] [Fintype H]

/-- An element of `Q` centralising all of `Q` (i.e. of `Z(Q)`) centralises all of `H`:
it centralises `P` by the hypothesis `Q ⊓ C_H(Q) = Q ⊓ C_H(P)` and every element of `H` is a
product `q * s` with `q ∈ Q`, `s ∈ P`. -/
theorem part2_mem_center_of_mem_inf {Q P : Subgroup H} (hQn : Q.Normal) (hsup : P ⊔ Q = ⊤)
    (hcp : Q ⊓ Subgroup.centralizer (P : Set H) = Q ⊓ Subgroup.centralizer (Q : Set H))
    {z : H} (hz : z ∈ Q ⊓ Subgroup.centralizer (Q : Set H)) : z ∈ Subgroup.center H := by
  have hzP : z ∈ Subgroup.centralizer (P : Set H) := by
    have h2 : z ∈ Q ⊓ Subgroup.centralizer (P : Set H) := by rw [hcp]; exact hz
    exact h2.2
  have hzQ : z ∈ Subgroup.centralizer (Q : Set H) := hz.2
  rw [Subgroup.mem_center_iff]
  intro h
  have hmem : h ∈ Q ⊔ P := by rw [sup_comm, hsup]; exact Subgroup.mem_top h
  obtain ⟨q, hq, s, hs, rfl⟩ := (Subgroup.mem_sup_of_normal_left (s := Q) (t := P)).mp hmem
  have h1 : z * q = q * z := (Subgroup.mem_centralizer_iff.mp hzQ q hq).symm
  have h2 : z * s = s * z := (Subgroup.mem_centralizer_iff.mp hzP s hs).symm
  calc q * s * z = q * (s * z) := by rw [mul_assoc]
    _ = q * (z * s) := by rw [← h2]
    _ = q * z * s := by rw [mul_assoc]
    _ = z * q * s := by rw [← h1]
    _ = z * (q * s) := by rw [mul_assoc]

/-- A finite group of prime order is commutative. -/
theorem part2_isMulCommutative_of_natCard_prime {G : Type*} [Group G] {p : ℕ} (hp : p.Prime)
    (hcard : Nat.card G = p) : IsMulCommutative G := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hcyc : IsCyclic G := isCyclic_of_prime_card hcard
  rw [isMulCommutative_iff]
  intro a b
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hg a)
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hg b)
  rw [← hm, ← hn]
  exact zpow_mul_comm g m n

/-- For an irreducible character, `‖χ 1‖²` is the square of the degree. -/
theorem part2_normSq_apply_one {G : Type*} [Group G] [Fintype G] {χ : G → ℂ}
    (hχ : χ ∈ Work.CharCore.Irr G) :
    Complex.normSq (χ 1) = (Work.CharCore.irrDeg χ : ℝ) ^ 2 := by
  rw [Work.CharCore.irrDeg_spec hχ]
  have h2 : ((Work.CharCore.irrDeg χ : ℕ) : ℂ) = (((Work.CharCore.irrDeg χ : ℕ) : ℝ) : ℂ) := by
    push_cast; ring
  rw [h2, Complex.normSq_ofReal]
  ring

/-- A character whose kernel does not contain `Z(Q)` is not linear: if `χ` had degree one it
would be a homomorphism to the commutative group `ℂˣ`, hence trivial on
`⁅H,H⁆ ⊇ ⁅P,Q⁆ = Q ∋ z`. -/
theorem part2_irrDeg_ne_one {Q P : Subgroup H} (hqp : ⁅P, Q⁆ = Q) {χ : H → ℂ}
    (hχ : χ ∈ Work.CharCore.Irr H)
    (hZ : ∃ z ∈ Q ⊓ Subgroup.centralizer (Q : Set H), χ z ≠ χ 1) :
    Work.CharCore.irrDeg χ ≠ 1 := by
  intro hdeg
  obtain ⟨φ, hφ⟩ := (Work.CharCore.linear_char_iff_deg_one hχ).mp hdeg
  have hker : Q ≤ φ.ker := by
    have hcomm_le : ⁅(⊤ : Subgroup H), (⊤ : Subgroup H)⁆ ≤ φ.ker := by
      rw [Subgroup.commutator_le]
      intro a _ b _
      rw [MonoidHom.mem_ker, map_commutatorElement]
      exact commutatorElement_eq_one_iff_mul_comm.mpr (mul_comm _ _)
    calc Q = ⁅P, Q⁆ := hqp.symm
      _ ≤ ⁅(⊤ : Subgroup H), (⊤ : Subgroup H)⁆ := Subgroup.commutator_mono le_top le_top
      _ ≤ φ.ker := hcomm_le
  obtain ⟨z, hz, hzne⟩ := hZ
  have hzker : φ z = 1 := MonoidHom.mem_ker.mp (hker hz.1)
  have h1 : χ z = 1 := by rw [hφ z, hzker]; rfl
  have h2 : χ 1 = 1 := by rw [hφ 1, map_one]; rfl
  exact hzne (by rw [h1, h2])

theorem part2 {H : Type*} [Group H] [Fintype H] {q p m : ℕ} (Q P : Subgroup H) [Fintype ↥P] (hQn : Q.Normal) (hinf : P ⊓ Q = ⊥) (hsup : P ⊔ Q = ⊤) (hq : q.Prime) (hQext : Work.PGroup.IsExtraspecial q Q) (hcardQ : Nat.card Q = q ^ (2 * m + 1)) (hqodd : Odd q) (hp : p.Prime) (hPcard : Nat.card P = p) (hpQ : ¬ p ∣ Nat.card Q) (hqp : ⁅P, Q⁆ = Q) (hcp : Q ⊓ Subgroup.centralizer (P : Set H) = Q ⊓ Subgroup.centralizer (Q : Set H)) {χ : H → ℂ} (hχ : χ ∈ Work.CharCore.Irr H) (hZ : ∃ z ∈ Q ⊓ Subgroup.centralizer (Q : Set H), χ z ≠ χ 1) : (∑ s : P, χ (s : H)) ≠ 0 := by
  classical
  -- ## Clifford's theorem: `Res_Q χ = e • orbitSum Q θ`
  have hχC : χ ∈ Work.Clifford.Irr H := (Work.Clifford.corr_mem_Irr_charCore).mpr hχ
  obtain ⟨θ, hθ, e, he, hres⟩ := Work.Clifford.clifford_decomposition (N := Q) hχC
  have hθC : θ ∈ Work.CharCore.Irr ↥Q := (Work.Clifford.corr_mem_Irr_charCore).mp hθ
  -- ## The two inputs coming from the group theory of the configuration
  -- central elements of `Q` act as scalars
  have hscalar : ∀ z : H, z ∈ Q ⊓ Subgroup.centralizer (Q : Set H) →
      ∃ ω : ℂ, ω * starRingEnd ℂ ω = 1 ∧ ∀ x : H, χ (z * x) = ω * χ x :=
    fun z hz => part2_central_scalar hχ (part2_mem_center_of_mem_inf hQn hsup hcp hz)
  -- `‖χ‖²` is constant on the cosets `Q s`, `s ∈ P^#`
  have hcoset : ∀ (s : ↥P), s ≠ 1 → ∀ u : ↥Q,
      Complex.normSq (χ ((u : H) * (s : H))) = Complex.normSq (χ (s : H)) :=
    fun s hs u => part2_coset_value_self Q P hQn hinf hsup hq hQext hp hPcard hpQ hcp hχ hscalar hs u
  have hne1 : Work.CharCore.irrDeg χ ≠ 1 := part2_irrDeg_ne_one hqp hχ hZ
  by_cases hinv : Work.Clifford.inertia Q θ = ⊤
  · -- ## Case 1: `θ` is `H`-invariant (the inertia subgroup is all of `H`)
    obtain ⟨he1, hresθ⟩ :=
      part2_res_eq_of_invariant Q P hQn hinf hsup hp hPcard hχ hθ hinv hres
    have hk1 : (Work.Clifford.charOrbit Q θ).card = 1 := by
      rw [Work.Clifford.card_charOrbit, hinv]
      exact Subgroup.index_eq_one.mpr rfl
    have hcount0 := part2_count Q P hQn hinf hsup hPcard hχ hθ he hres hcoset
    have hcount : ∑ s : ↥P, Complex.normSq (χ (s : H))
        = (Work.CharCore.irrDeg χ : ℝ) ^ 2 + ((p : ℝ) - 1) := by
      rw [hcount0, he1, hk1]
      norm_num
    have hdeg : Work.CharCore.irrDeg χ = Work.CharCore.irrDeg θ := by
      have h1 : χ (1 : H) = θ 1 := by
        have h := congrFun hresθ (1 : ↥Q)
        simpa using h
      rw [Work.CharCore.irrDeg_spec hχ, Work.CharCore.irrDeg_spec hθC] at h1
      exact Nat.cast_injective h1
    have hpow : ∃ j : ℕ, Work.CharCore.irrDeg χ = q ^ j := by
      have hdvd : Work.CharCore.irrDeg θ ∣ Nat.card ↥Q :=
        Work.CharCore.irr_degree_dvd_card hθC
      have hcard : Nat.card ↥Q = q ^ (2 * m + 1) := hcardQ
      rw [hcard] at hdvd
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hq).mp hdvd
      exact ⟨j, by rw [hdeg, hj]⟩
    have hcomm : IsMulCommutative ↥P := part2_isMulCommutative_of_natCard_prime hp hPcard
    exact part2_final_step hp hPcard hcomm hq hqodd hχ hcount hpow hne1
  · -- ## Case 2: the inertia subgroup is `Q`; the orbit of `θ` has size `p`
    have hk : (Work.Clifford.charOrbit Q θ).card = p := by
      have hQle : Q ≤ Work.Clifford.inertia Q θ := Work.Clifford.le_inertia_of_mem_Irr hθ
      have hdvd : (Work.Clifford.inertia Q θ).index ∣ Q.index := Subgroup.index_dvd_of_le hQle
      have hQindex : Q.index = p := by
        have h := (part2_quotient_cyclic Q P hQn hinf hsup hp hPcard).2
        rw [Subgroup.index_eq_card, h]
      rw [hQindex] at hdvd
      have hne : (Work.Clifford.inertia Q θ).index ≠ 1 :=
        fun h => hinv (Subgroup.index_eq_one.mp h)
      rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | h1
      · exact absurd h1 hne
      · rw [Work.Clifford.card_charOrbit]; exact h1
    have hcount := part2_count Q P hQn hinf hsup hPcard hχ hθ he hres hcoset
    -- the count reads `∑_P ‖χ‖² = d² + (p - e²p)`; the sum dominates `‖χ 1‖² = d²`
    have hnorm1 : Complex.normSq (χ 1) = (Work.CharCore.irrDeg χ : ℝ) ^ 2 :=
      part2_normSq_apply_one hχ
    have hle : (Work.CharCore.irrDeg χ : ℝ) ^ 2 ≤ ∑ s : ↥P, Complex.normSq (χ (s : H)) := by
      have hsingle : Complex.normSq (χ ((1 : ↥P) : H))
          ≤ ∑ s : ↥P, Complex.normSq (χ (s : H)) :=
        Finset.single_le_sum (f := fun s : ↥P => Complex.normSq (χ (s : H)))
          (fun i _ => Complex.normSq_nonneg _) (Finset.mem_univ (1 : ↥P))
      rw [← hnorm1]
      simpa using hsingle
    have hsum : ∑ s : ↥P, Complex.normSq (χ (s : H))
        = (Work.CharCore.irrDeg χ : ℝ) ^ 2 + ((p : ℝ) - (e : ℝ) ^ 2 * (p : ℝ)) := by
      rw [hcount, hk]
    -- hence `e = 1`
    have he1 : e = 1 := by
      have hp_pos : (0 : ℝ) < p := by exact_mod_cast hp.pos
      have hle' : (Work.CharCore.irrDeg χ : ℝ) ^ 2 ≤
          (Work.CharCore.irrDeg χ : ℝ) ^ 2 + ((p : ℝ) - (e : ℝ) ^ 2 * (p : ℝ)) := by
        rw [← hsum]; exact hle
      have h1 : (e : ℝ) ^ 2 * (p : ℝ) ≤ (p : ℝ) := by linarith
      have h2 : (e : ℝ) ^ 2 ≤ 1 := by
        have h1' : (e : ℝ) ^ 2 * (p : ℝ) ≤ (1 : ℝ) * (p : ℝ) := by rw [one_mul]; exact h1
        exact (mul_le_mul_iff_of_pos_right hp_pos).mp h1'
      have h3 : (e : ℝ) ≤ 1 := by nlinarith [sq_nonneg ((e : ℝ) - 1), h2]
      have h4 : (1 : ℝ) ≤ (e : ℝ) := by exact_mod_cast he
      have h5 : (e : ℝ) = 1 := le_antisymm h3 h4
      exact_mod_cast h5
    -- so `∑_P ‖χ‖² = d² = ‖χ 1‖²`, and every term is nonnegative
    have hsum2 : ∑ s : ↥P, Complex.normSq (χ (s : H))
        = Complex.normSq (χ ((1 : ↥P) : H)) := by
      rw [hsum, he1]
      rw [show Complex.normSq (χ ((1 : ↥P) : H)) = (Work.CharCore.irrDeg χ : ℝ) ^ 2 from by
        simpa using hnorm1]
      ring
    have hvanish : ∀ s : ↥P, s ≠ 1 → χ (s : H) = 0 := by
      intro s hs
      have hsum0 : ∑ t ∈ (Finset.univ.erase (1 : ↥P)), Complex.normSq (χ (t : H)) = 0 := by
        have hsplit := Finset.sum_erase_add (Finset.univ : Finset ↥P)
          (fun t : ↥P => Complex.normSq (χ (t : H))) (Finset.mem_univ (1 : ↥P))
        rw [hsum2] at hsplit
        linarith
      have hmem : s ∈ Finset.univ.erase (1 : ↥P) :=
        Finset.mem_erase.mpr ⟨hs, Finset.mem_univ s⟩
      have hz : Complex.normSq (χ (s : H)) = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => Complex.normSq_nonneg _)).mp hsum0 s hmem
      exact Complex.normSq_eq_zero.mp hz
    have hsumfin : ∑ s : ↥P, χ (s : H) = χ (1 : H) := by
      rw [← Finset.sum_erase_add (Finset.univ : Finset ↥P) (fun t : ↥P => χ (t : H))
        (Finset.mem_univ (1 : ↥P))]
      rw [Finset.sum_eq_zero (fun t ht => hvanish t (Finset.mem_erase.mp ht).1)]
      simp
    rw [hsumfin, Work.CharCore.irrDeg_spec hχ]
    exact_mod_cast (Work.CharCore.irrDeg_pos hχ).ne'

end Work.Hering.AppVII
