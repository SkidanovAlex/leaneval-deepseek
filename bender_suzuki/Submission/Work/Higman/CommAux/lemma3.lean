import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.homogeneous_structure
import Submission.Work.Higman.suzuki_unipotence
import Submission.Work.Higman.higman_lemma1
import Submission.Work.Higman.higman_lemma2
import Submission.Work.Higman.lemma3_core
import Submission.Work.Higman.boolean_idempotent_family
import Submission.Work.Higman.xi_trans_quot_sq
import Submission.Work.Higman.CommAux.defs
import Submission.Work.Higman.powSub_normal
import Submission.Work.Higman.CommAux.nu_add

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped commutatorElement

set_option maxHeartbeats 4000000

namespace Work.Higman.CommAux

open Work.Higman

variable {P : Type} [Group P] [Finite P]

/-! ## Idempotence of `ν`, and its `ξ`-equivariance, modulo `A ^ (2)`

`ν_u(a) = l3Sqrt h hA u a` is the square root in `A` of the conjugation derivation
`Δ_u(a) = u⁻¹ a u a⁻¹`.  Two computations are needed for the endomorphism `ν̄(u)` of
`A / A ^ (2)`:

* `ν_u(ν_u a) ≡ ν_u(a)⁻¹  (mod A²)`, i.e. `ν̄(u)` is idempotent (in characteristic `2`);
* `ν_{ξu}(ξa) ≡ ξ(ν_u a)  (mod A²)`, i.e. `ν̄` is `ξ`-equivariant. -/

/-- `Δ_u` is a homomorphism, multiplicatively. -/
theorem l3Delta_mul_apply' {A : Subgroup P} (hAn : A.Normal)
    (hAb : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (u : P) (b c : ↥A) :
    ((l3Delta hAn hAb u (b * c) : ↥A) : P)
      = ((l3Delta hAn hAb u b : ↥A) : P) * ((l3Delta hAn hAb u c : ↥A) : P) := by
  rw [l3Delta_apply, l3Delta_apply, l3Delta_apply]
  exact l3Delta_mul_apply hAn hAb u b.2 c.2

/-- **Idempotence of `ν̄`.**  If `u * u ∈ A` and `hA4` is the statement that fourth powers in
`A` vanish only in `A ^ (2)`, then `ν_u(ν_u a) * ν_u a ∈ A ^ (2)`. -/
theorem nu_idem_L3 (h : IsSuzuki2Grp P) {A : Subgroup P} (hA : IsXiAbelNormal h A)
    (hA4 : ∀ x ∈ A, x ^ 4 = 1 → x ∈ powSub A 2)
    {u : P} (hu : u * u ∈ A) (a : ↥A) :
    ((l3Sqrt h hA u (l3Sqrt h hA u a) : ↥A) : P)
      * ((l3Sqrt h hA u a : ↥A) : P) ∈ powSub A 2 := by
  have hAn : A.Normal := hA.normal
  have hAb : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := hA.abelian
  set x : P := ((l3Sqrt h hA u (l3Sqrt h hA u a) : ↥A) : P) with hxdef
  set y : P := ((l3Sqrt h hA u a : ↥A) : P) with hydef
  have hxA : x ∈ A := (l3Sqrt h hA u (l3Sqrt h hA u a)).2
  have hyA : y ∈ A := (l3Sqrt h hA u a).2
  have hx2 : x * x = ((l3Delta hAn hAb u ⟨y, hyA⟩ : ↥A) : P) := by
    rw [l3Sqrt_sq h hA u (l3Sqrt h hA u a), l3Delta_apply]
  have hy2 : y * y = u⁻¹ * (a : P) * u * (a : P)⁻¹ := l3Sqrt_sq h hA u a
  have hyy : (⟨y, hyA⟩ : ↥A) * (⟨y, hyA⟩ : ↥A) = (l3Delta hAn hAb u a) := by
    apply Subtype.ext
    show y * y = ((l3Delta hAn hAb u a : ↥A) : P)
    rw [hy2, l3Delta_apply]
  -- `x ^ 4 = Δ_u (Δ_u a)`
  have hx4 : x ^ 4 = ((l3Delta hAn hAb u (l3Delta hAn hAb u a) : ↥A) : P) := by
    rw [show x ^ 4 = (x * x) * (x * x) from by
      rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul]
      simp only [pow_two]]
    rw [hx2, ← l3Delta_mul_apply' hAn hAb u ⟨y, hyA⟩ ⟨y, hyA⟩, hyy]
  have hDa : ((l3Delta hAn hAb u a : ↥A) : P) = y * y :=
    (l3Delta_apply hAn hAb u a).trans hy2.symm
  have hx4' : x ^ 4 = (y ^ 4)⁻¹ := by
    rw [hx4, l3Delta_delta h hA hu a, hDa]
    group
  have hcomm : Commute x y := hAb x hxA y hyA
  have hxy4 : (x * y) ^ 4 = 1 := by
    rw [hcomm.mul_pow, hx4', inv_mul_cancel]
  exact hA4 (x * y) (A.mul_mem hxA hyA) hxy4

/-- **`ξ`-equivariance of `ν̄`.**  `ν_{ξu}(ξa) ≡ ξ(ν_u(a))` modulo `A ^ (2)`. -/
theorem nu_eqv_L3 (h : IsSuzuki2Grp P) {A : Subgroup P} (hA : IsXiAbelNormal h A)
    (hAinv : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hA2 : ∀ x ∈ A, x * x = 1 → x ∈ powSub A 2)
    (u : P) (a : ↥A) :
    ((l3Sqrt h hA (h.xi u) (xiSub h hAinv a) : ↥A) : P)
      * (h.xi ((l3Sqrt h hA u a : ↥A) : P))⁻¹ ∈ powSub A 2 := by
  have hAb : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := hA.abelian
  have hxA : ((l3Sqrt h hA (h.xi u) (xiSub h hAinv a) : ↥A) : P) ∈ A :=
    (l3Sqrt h hA (h.xi u) (xiSub h hAinv a)).2
  have hyA : h.xi ((l3Sqrt h hA u a : ↥A) : P) ∈ A := by
    have hmem := Subgroup.mem_map_of_mem (h.xi : MulAut P).toMonoidHom (l3Sqrt h hA u a).2
    rwa [hAinv] at hmem
  refine l3_mul_inv_mem_powSub_two hAb hA2 hxA hyA ?_
  rw [l3Sqrt_sq h hA (h.xi u) (xiSub h hAinv a), xiSub_coe, ← map_mul,
    l3Sqrt_sq h hA u a]
  simp only [map_mul, map_inv]

/-- Pure arithmetic: a power of `q ≥ 4` cannot be exactly twice another power of `q`. -/
theorem pow_eq_two_mul_pow_contra {q e s t : ℕ} (hq : 4 ≤ q) (hs : s ≤ e) (ht : t ≤ e)
    (h : q ^ (e - s) = 2 * q ^ (e - t)) : False := by
  have hq0 : 0 < q := by omega
  by_cases hts : t ≤ s
  · have hle : q ^ (e - s) ≤ q ^ (e - t) := Nat.pow_le_pow_right hq0 (by omega)
    have h1 : 2 * q ^ (e - s) ≤ q ^ (e - s) := by
      calc 2 * q ^ (e - s) ≤ 2 * q ^ (e - t) := Nat.mul_le_mul_left 2 hle
        _ = q ^ (e - s) := h.symm
    have := pow_pos hq0 (e - s)
    omega
  · rw [not_le] at hts
    have hsplit : e - s = (t - s) + (e - t) := by omega
    rw [hsplit, pow_add] at h
    have h2 : q ^ (t - s) = 2 :=
      Nat.eq_of_mul_eq_mul_right (pow_pos hq0 (e - t)) h
    have h3 : 4 ≤ q ^ (t - s) :=
      calc (4 : ℕ) ≤ q := hq
        _ = q ^ 1 := (pow_one q).symm
        _ ≤ q ^ (t - s) := Nat.pow_le_pow_right hq0 (by omega)
    omega

/-- **The homocyclic tower forbids an index-two pair of `ξ`-invariant subgroups.**  If `A` is a
`ξ`-invariant abelian subgroup of a Suzuki 2-group with `Ω₁(P) ≤ A`, then `ξ`-invariant
subgroups of `A` form the strictly decreasing tower `A = A^{(1)} > A^{(2)} > A^{(4)} > ⋯` whose
successive quotients all have order `|A ⊓ Ω₁(P)| ≥ 4`; hence no two of them can satisfy
`|B| = 2 |F|`. -/
theorem tower_contra_L3 (h : IsSuzuki2Grp P) {A B F : Subgroup P}
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hAinv : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hB : B ≤ A) (hBinv : B.map (h.xi : MulAut P).toMonoidHom = B)
    (hF : F ≤ A) (hFinv : F.map (h.xi : MulAut P).toMonoidHom = F)
    (hFB : F ≤ B) (hcard : Nat.card ↥B = 2 * Nat.card ↥F)
    (hOm : omega1 P ≤ A) : False := by
  obtain ⟨e, he1, hchain, -, hstruct⟩ := homogeneous_structure h hAab hAinv
  have hq4 : 4 ≤ Nat.card ↥(A ⊓ omega1 P) := by
    rw [inf_eq_right.mpr hOm]; exact h.omega1_card_ge_four
  -- normalise the exponents of the two tower members
  have hnorm : ∀ i : ℕ, powSub A (2 ^ i) = powSub A (2 ^ min i e) := by
    intro i
    by_cases hi : i ≤ e
    · rw [min_eq_left hi]
    · rw [not_le] at hi
      rw [min_eq_right (le_of_lt hi),
        powSub_eq_bot_of_exp (A := A) hAab (e := e) (k := i) (le_of_lt hi) he1,
        powSub_eq_bot_of_exp (A := A) hAab (e := e) (k := e) le_rfl he1]
  obtain ⟨s, hs⟩ := hstruct B hB hBinv
  obtain ⟨t, ht⟩ := hstruct F hF hFinv
  have hBcard : Nat.card ↥B = (Nat.card ↥(A ⊓ omega1 P)) ^ (e - min s e) := by
    rw [hs, hnorm s]
    exact hchain (min s e) (min_le_right _ _)
  have hFcard : Nat.card ↥F = (Nat.card ↥(A ⊓ omega1 P)) ^ (e - min t e) := by
    rw [ht, hnorm t]
    exact hchain (min t e) (min_le_right _ _)
  exact pow_eq_two_mul_pow_contra (q := Nat.card ↥(A ⊓ omega1 P)) (e := e)
    (s := min s e) (t := min t e) hq4 (min_le_right _ _) (min_le_right _ _)
    (by rw [← hBcard, ← hFcard]; exact hcard)

/-- **The final step of Higman's Lemma 3** (Higman 1963, p. 84).  Let `A ⊴ P` be a
`ξ`-invariant abelian normal subgroup of a Suzuki 2-group with `Ω₁(P) ≤ A`, let `C ≥ A` be a
`ξ`-invariant normal subgroup with `C² ≤ A²`, and let `u ∈ C ∖ A` be such that `C ∖ A = uA`.
Then we reach a contradiction: the endomorphism `a ↦ a·u⁻¹au` of `A` has image `FA`, the group
`B` generated by the squares of the elements of `C ∖ A` is `FA` or has exactly two `FA`-cosets,
and both alternatives are impossible (the first gives an involution of `C ∖ A`, the second
contradicts the homocyclic tower, `tower_contra_L3`). -/
theorem final_step_L3 (h : IsSuzuki2Grp P) {A C : Subgroup P} (hA : IsXiAbelNormal h A)
    (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C) (hAC : A ≤ C)
    (hC2 : powSub C 2 ≤ powSub A 2) (hOm : omega1 P ≤ A)
    (u : P) (hu : u ∈ C) (huna : u ∉ A)
    (hsep : ∀ v : P, v ∈ C → v ∉ A → v * u⁻¹ ∈ A) : False := by
  have hAn : A.Normal := hA.normal
  have hAb : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := hA.abelian
  have hAinv : A.map (h.xi : MulAut P).toMonoidHom = A := hA.map_eq
  have hC2A : powSub C 2 ≤ A := hC2.trans (powSub_le (n := 2) (by norm_num))
  have hu2A : u * u ∈ A := hC2A (by rw [← pow_two]; exact pow_mem_powSub hu)
  have hu2ne : u * u ≠ 1 := by
    intro h1
    exact huna (hOm (h.mem_omega1.mpr (by rw [pow_two]; exact h1)))
  -- ### the map `F : a ↦ a * (u⁻¹ * a * u)` on `A`, and its image `FA`
  have hFmem : ∀ a : ↥A, (a : P) * (u⁻¹ * (a : P) * u) ∈ A := fun a =>
    A.mul_mem a.2 (by simpa using hAn.conj_mem (a : P) a.2 u⁻¹)
  let Fh : ↥A →* ↥A :=
    { toFun := fun a => ⟨(a : P) * (u⁻¹ * (a : P) * u), hFmem a⟩
      map_one' := Subtype.ext (by show (1 : P) * (u⁻¹ * 1 * u) = 1; group)
      map_mul' := by
        intro a b
        apply Subtype.ext
        have ha : u⁻¹ * (a : P) * u ∈ A := by simpa using hAn.conj_mem (a : P) a.2 u⁻¹
        have hb : u⁻¹ * (b : P) * u ∈ A := by simpa using hAn.conj_mem (b : P) b.2 u⁻¹
        show ((a : P) * (b : P)) * (u⁻¹ * ((a : P) * (b : P)) * u)
            = ((a : P) * (u⁻¹ * (a : P) * u)) * ((b : P) * (u⁻¹ * (b : P) * u))
        rw [show u⁻¹ * ((a : P) * (b : P)) * u
            = (u⁻¹ * (a : P) * u) * (u⁻¹ * (b : P) * u) from by group]
        calc ((a : P) * (b : P)) * ((u⁻¹ * (a : P) * u) * (u⁻¹ * (b : P) * u))
            = (a : P) * ((b : P) * (u⁻¹ * (a : P) * u)) * (u⁻¹ * (b : P) * u) := by group
          _ = (a : P) * ((u⁻¹ * (a : P) * u) * (b : P)) * (u⁻¹ * (b : P) * u) := by
                rw [hAb (b : P) b.2 _ ha]
          _ = ((a : P) * (u⁻¹ * (a : P) * u)) * ((b : P) * (u⁻¹ * (b : P) * u)) := by group }
  have hFh_apply : ∀ a : ↥A, ((Fh a : ↥A) : P) = (a : P) * (u⁻¹ * (a : P) * u) := fun a => rfl
  let FA : Subgroup P := (Fh.range).map A.subtype
  have hFAmem : ∀ x : P, x ∈ FA ↔ ∃ a : ↥A, ((Fh a : ↥A) : P) = x := by
    intro x
    constructor
    · rintro ⟨y, hy, hyx⟩
      obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hy
      exact ⟨a, hyx⟩
    · rintro ⟨a, rfl⟩
      exact Subgroup.mem_map_of_mem _ (MonoidHom.mem_range.mpr ⟨a, rfl⟩)
  have hFAleA : FA ≤ A := by
    rintro x ⟨y, -, hyx⟩
    rw [← hyx]
    exact y.2
  -- the basic computation `(u * b) ^ 2 = u ^ 2 * F b`
  have hu4FA : (u * u) * (u * u) ∈ FA := (hFAmem _).mpr ⟨⟨u * u, hu2A⟩, by
    rw [hFh_apply]
    show (u * u) * (u⁻¹ * (u * u) * u) = (u * u) * (u * u)
    rw [show u⁻¹ * (u * u) * u = u * u from by group]⟩
  have hFsq : ∀ b ∈ A, (u * b) ^ 2 = (u * u) * (b * (u⁻¹ * b * u)) := by
    intro b hb
    have hb' : u⁻¹ * b * u ∈ A := by simpa using hAn.conj_mem b hb u⁻¹
    calc (u * b) ^ 2 = (u * b) * (u * b) := pow_two _
      _ = (u * u) * ((u⁻¹ * b * u) * b) := by group
      _ = (u * u) * (b * (u⁻¹ * b * u)) := by rw [hAb b hb _ hb']
  have hFsqF : ∀ (b : P) (hb : b ∈ A), (u * b) ^ 2 = (u * u) * ((Fh ⟨b, hb⟩ : ↥A) : P) := by
    intro b hb
    rw [hFsq b hb, hFh_apply]
  -- ### `B`: the subgroup generated by the squares of the elements of `C ∖ A`
  let B : Subgroup P := Subgroup.closure {x : P | ∃ c ∈ C, c ∉ A ∧ ∃ a ∈ A, (c * a) ^ 2 = x}
  have hBdef : B = Subgroup.closure {x : P | ∃ c ∈ C, c ∉ A ∧ ∃ a ∈ A, (c * a) ^ 2 = x} := rfl
  have hBleA : B ≤ A := by
    rw [hBdef, Subgroup.closure_le]
    rintro x ⟨c, hcC, -, a, haA, rfl⟩
    have h1 : c * c ∈ A := hC2A (by rw [← pow_two]; exact pow_mem_powSub hcC)
    have h2 : c⁻¹ * a * c ∈ A := by simpa using hAn.conj_mem a haA c⁻¹
    rw [show (c * a) ^ 2 = (c * c) * ((c⁻¹ * a * c) * a) from by rw [pow_two]; group]
    exact A.mul_mem h1 (A.mul_mem h2 haA)
  have hgen_mem : ∀ c ∈ C, c ∉ A → ∀ a ∈ A, (c * a) ^ 2 ∈ B := fun c hcC hcA a haA =>
    Subgroup.subset_closure ⟨c, hcC, hcA, a, haA, rfl⟩
  have hu2B : u * u ∈ B := by
    simpa [pow_two] using hgen_mem u hu huna 1 A.one_mem
  have hFAleB : FA ≤ B := by
    intro x hx
    obtain ⟨a, rfl⟩ := (hFAmem x).mp hx
    have hgen : (u * (a : P)) ^ 2 ∈ B := hgen_mem u hu huna _ a.2
    have hkey : ((Fh a : ↥A) : P) = (u * u)⁻¹ * (u * (a : P)) ^ 2 := by
      rw [hFh_apply, hFsq (a : P) a.2]
      group
    rw [hkey]
    exact B.mul_mem (B.inv_mem hu2B) hgen
  -- ### every element of `C ∖ A` is `u` times an element of `A`
  have hcoset : ∀ c ∈ C, c ∉ A → ∃ a ∈ A, c = u * a := by
    intro c hcC hcA
    refine ⟨u⁻¹ * (c * u⁻¹) * u, ?_, by group⟩
    simpa using hAn.conj_mem (c * u⁻¹) (hsep c hcC hcA) u⁻¹
  -- ### the `ξ`-invariance of `FA` and of `B`
  have hξuC : h.xi u ∈ C := by
    have hmem := Subgroup.mem_map_of_mem (h.xi : MulAut P).toMonoidHom hu
    rwa [hCinv] at hmem
  have hξuA : h.xi u ∉ A := by
    intro hc
    exact huna (by simpa using symm_mem_of_map_eq h.xi hAinv hc)
  obtain ⟨a₀, ha₀A, ha₀eq⟩ := hcoset (h.xi u) hξuC hξuA
  have hconj_eq : ∀ b ∈ A, (h.xi u)⁻¹ * b * (h.xi u) = u⁻¹ * b * u := by
    intro b hb
    have h1 : u⁻¹ * b * u ∈ A := by simpa using hAn.conj_mem b hb u⁻¹
    calc (h.xi u)⁻¹ * b * (h.xi u) = a₀⁻¹ * (u⁻¹ * b * u) * a₀ := by rw [ha₀eq]; group
      _ = u⁻¹ * b * u := by rw [hAb a₀⁻¹ (A.inv_mem ha₀A) _ h1]; group
  have hstep : ∀ a : ↥A, h.xi (((Fh a : ↥A) : P)) = ((Fh (xiSub h hAinv a) : ↥A) : P) := by
    intro a
    have hξa : h.xi (a : P) ∈ A := by
      have hmem := Subgroup.mem_map_of_mem (h.xi : MulAut P).toMonoidHom a.2
      rwa [hAinv] at hmem
    rw [hFh_apply, hFh_apply, xiSub_coe, map_mul]
    congr 1
    show h.xi (u⁻¹ * (a : P) * u) = u⁻¹ * h.xi (a : P) * u
    rw [map_mul, map_mul, map_inv]
    exact hconj_eq (h.xi (a : P)) hξa
  have hFAinv : FA.map (h.xi : MulAut P).toMonoidHom = FA := by
    have hle : FA.map (h.xi : MulAut P).toMonoidHom ≤ FA := by
      rintro x ⟨y, hy, rfl⟩
      obtain ⟨a, rfl⟩ := (hFAmem y).mp hy
      exact (hFAmem _).mpr ⟨xiSub h hAinv a, (hstep a).symm⟩
    exact Subgroup.eq_of_le_of_card_ge hle (le_of_eq (Nat.card_congr
      (FA.equivMapOfInjective (h.xi : MulAut P).toMonoidHom h.xi.injective).toEquiv))
  have hBinv_le : B.map (h.xi : MulAut P).toMonoidHom ≤ B := by
    rw [Subgroup.map_le_iff_le_comap, hBdef, Subgroup.closure_le]
    rintro x ⟨c, hcC, hcA, a, haA, rfl⟩
    change h.xi ((c * a) ^ 2) ∈ B
    have hξcC : h.xi c ∈ C := by
      have hmem := Subgroup.mem_map_of_mem (h.xi : MulAut P).toMonoidHom hcC
      rwa [hCinv] at hmem
    have hξcA : h.xi c ∉ A := by
      intro hc
      exact hcA (by simpa using symm_mem_of_map_eq h.xi hAinv hc)
    have hξaA : h.xi a ∈ A := by
      have hmem := Subgroup.mem_map_of_mem (h.xi : MulAut P).toMonoidHom haA
      rwa [hAinv] at hmem
    rw [map_pow, map_mul]
    exact hgen_mem (h.xi c) hξcC hξcA (h.xi a) hξaA
  have hBinv : B.map (h.xi : MulAut P).toMonoidHom = B :=
    Subgroup.eq_of_le_of_card_ge hBinv_le (le_of_eq (Nat.card_congr
      (B.equivMapOfInjective (h.xi : MulAut P).toMonoidHom h.xi.injective).toEquiv))
  by_cases hu2FA : u * u ∈ FA
  · -- ## Case (i): `u ^ 2 ∈ FA` produces an involution in `C ∖ A`
    obtain ⟨a₀', ha₀'⟩ := (hFAmem (u * u)).mp hu2FA
    have hFainv : ((Fh a₀'⁻¹ : ↥A) : P) = ((Fh a₀' : ↥A) : P)⁻¹ :=
      congrArg (fun t : ↥A => (t : P)) (map_inv Fh a₀')
    have hw2 : (u * (a₀' : P)⁻¹) ^ 2 = 1 := by
      rw [hFsqF (a₀' : P)⁻¹ (A.inv_mem a₀'.2),
        show (⟨(a₀' : P)⁻¹, A.inv_mem a₀'.2⟩ : ↥A) = a₀'⁻¹ from Subtype.ext rfl,
        hFainv, ha₀']
      exact mul_inv_cancel _
    have hwC : u * (a₀' : P)⁻¹ ∈ C := C.mul_mem hu (C.inv_mem (hAC a₀'.2))
    have hwA : u * (a₀' : P)⁻¹ ∉ A := by
      intro hw
      exact huna (by
        have : u = (u * (a₀' : P)⁻¹) * a₀' := by group
        rw [this]; exact A.mul_mem hw a₀'.2)
    exact hwA (hOm (h.mem_omega1.mpr hw2))
  · -- ## Case (ii): `B` has exactly two `FA`-cosets
    have hFA'normal : (FA.subgroupOf A).Normal :=
      Subgroup.Normal.mk fun n hn g => by
        have hnA : ((n : ↥A) : P) ∈ FA := Subgroup.mem_subgroupOf.mp hn
        rw [Subgroup.mem_subgroupOf]
        have hgn : (g * n * g⁻¹ : ↥A) = n := Subtype.ext (by
          show (g : P) * (n : P) * (g : P)⁻¹ = (n : P)
          rw [hAb (g : P) g.2 (n : P) (hFAleA hnA)]
          group)
        rw [hgn]
        exact hnA
    let f : ↥B →* (↥A ⧸ FA.subgroupOf A) :=
      { toFun := fun x => QuotientGroup.mk ((Subgroup.inclusion hBleA x : ↥A))
        map_one' := by
          show QuotientGroup.mk ((Subgroup.inclusion hBleA (1 : ↥B) : ↥A)) = 1
          rw [map_one, QuotientGroup.eq_one_iff]
          exact (FA.subgroupOf A).one_mem
        map_mul' := by
          intro x y
          show QuotientGroup.mk ((Subgroup.inclusion hBleA (x * y) : ↥A))
            = QuotientGroup.mk ((Subgroup.inclusion hBleA x : ↥A))
              * QuotientGroup.mk ((Subgroup.inclusion hBleA y : ↥A))
          rw [map_mul, QuotientGroup.mk_mul] }
    have hfker : ∀ x : ↥B, x ∈ f.ker ↔ (x : P) ∈ FA := by
      intro x
      rw [MonoidHom.mem_ker]
      show QuotientGroup.mk ((Subgroup.inclusion hBleA x : ↥A)) = 1 ↔ (x : P) ∈ FA
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact Iff.rfl
    have hker : Nat.card ↥(f.ker) = Nat.card ↥FA := by
      refine Nat.card_congr (Equiv.ofBijective
        (fun x : ↥(f.ker) => (⟨(x.1 : P), (hfker x.1).mp x.2⟩ : ↥FA)) ⟨?_, ?_⟩)
      · intro x y hxy
        exact Subtype.ext (Subtype.ext (congrArg (fun t : ↥FA => (t : P)) hxy))
      · intro y
        have hyB : (y : P) ∈ B := hFAleB y.2
        exact ⟨⟨⟨(y : P), hyB⟩, (hfker ⟨(y : P), hyB⟩).mpr y.2⟩, Subtype.ext rfl⟩
    have hfgen : ∀ (c : P) (hcC : c ∈ C) (hcA : c ∉ A) (a : P) (haA : a ∈ A),
        f ⟨(c * a) ^ 2, hgen_mem c hcC hcA a haA⟩ = f ⟨u * u, hu2B⟩ := by
      intro c hcC hcA a haA
      obtain ⟨a₁, ha₁A, rfl⟩ := hcoset c hcC hcA
      have hu₁C : u * a₁ ∈ C := C.mul_mem hu (hAC ha₁A)
      have hu₁A : u * a₁ ∉ A := by
        intro hc
        exact huna (by
          have : u = (u * a₁) * a₁⁻¹ := by group
          rw [this]; exact A.mul_mem hc (A.inv_mem ha₁A))
      set a' : ↥A := ⟨a₁ * a, A.mul_mem ha₁A haA⟩ with ha'def
      have hval : (u * a₁ * a) ^ 2 = (u * u) * ((Fh a' : ↥A) : P) := by
        rw [mul_assoc, hFsqF (a₁ * a) (A.mul_mem ha₁A haA)]
      have hFAa' : ((Fh a' : ↥A) : P) ∈ FA := (hFAmem _).mpr ⟨a', rfl⟩
      have hsplit : (⟨(u * a₁ * a) ^ 2, hgen_mem (u * a₁) hu₁C hu₁A a haA⟩ : ↥B)
          = ⟨u * u, hu2B⟩ * ⟨((Fh a' : ↥A) : P), hFAleB hFAa'⟩ :=
        Subtype.ext (by
          show (u * a₁ * a) ^ 2 = (u * u) * _
          exact hval)
      rw [hsplit, map_mul]
      have hone : f ⟨((Fh a' : ↥A) : P), hFAleB hFAa'⟩ = 1 := by
        rw [← MonoidHom.mem_ker]
        exact (hfker _).mpr hFAa'
      rw [hone, mul_one]
    have hpow : ∀ (z : P) (hz : z ∈ B), f ⟨z, hz⟩ ∈ Subgroup.zpowers (f ⟨u * u, hu2B⟩) := by
      intro z hz
      induction hz using Subgroup.closure_induction with
      | mem y hy =>
          obtain ⟨c, hcC, hcA, a, haA, rfl⟩ := hy
          rw [hfgen c hcC hcA a haA]
          exact Subgroup.mem_zpowers _
      | one =>
          show f (1 : ↥B) ∈ Subgroup.zpowers (f ⟨u * u, hu2B⟩)
          rw [map_one]
          exact (Subgroup.zpowers _).one_mem
      | mul y z hy hz ihy ihz =>
          rw [show (⟨y * z, _⟩ : ↥B) = (⟨y, hy⟩ : ↥B) * ⟨z, hz⟩ from Subtype.ext rfl, map_mul]
          exact (Subgroup.zpowers _).mul_mem ihy ihz
      | inv y hy ihy =>
          rw [show (⟨y⁻¹, _⟩ : ↥B) = ((⟨y, hy⟩ : ↥B))⁻¹ from Subtype.ext rfl, map_inv]
          exact (Subgroup.zpowers _).inv_mem ihy
    have hrange2 : Nat.card ↥(f.range) = 2 := by
      have hrange_eq : f.range = Subgroup.zpowers (f ⟨u * u, hu2B⟩) := by
        apply le_antisymm
        · rintro y ⟨x, rfl⟩
          exact hpow (x : P) x.2
        · exact Subgroup.zpowers_le.mpr (MonoidHom.mem_range.mpr ⟨_, rfl⟩)
      rw [hrange_eq, Nat.card_zpowers]
      have h1 : (f ⟨u * u, hu2B⟩) ^ 2 = 1 := by
        rw [show (f ⟨u * u, hu2B⟩) ^ 2
            = f (⟨u * u, hu2B⟩ * ⟨u * u, hu2B⟩) from by
          rw [pow_two]; exact (map_mul f _ _).symm]
        rw [show (⟨u * u, hu2B⟩ * ⟨u * u, hu2B⟩ : ↥B)
            = ⟨(u * u) * (u * u), B.mul_mem hu2B hu2B⟩ from Subtype.ext rfl]
        rw [← MonoidHom.mem_ker]
        exact (hfker _).mpr hu4FA
      have h2 : f ⟨u * u, hu2B⟩ ≠ 1 := by
        intro hc
        exact hu2FA ((hfker _).mp hc)
      have hd : orderOf (f ⟨u * u, hu2B⟩) ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr h1
      rcases (Nat.dvd_prime Nat.prime_two).mp hd with h3 | h3
      · exact absurd (orderOf_eq_one_iff.mp h3) h2
      · exact h3
    have hcard : Nat.card ↥B = 2 * Nat.card ↥FA := by
      have h1 := Subgroup.card_mul_index f.ker
      rw [Subgroup.index_ker f] at h1
      rw [hker, hrange2] at h1
      omega
    exact tower_contra_L3 h hAb hAinv hBleA hBinv hFAleA hFAinv hFAleB hcard hOm

/-- **Idempotence of `ν̄` in the quotient `A / A²`.** -/
theorem nu_idem_mod (h : IsSuzuki2Grp P) {A : Subgroup P} (hA : IsXiAbelNormal h A)
    (hA4 : ∀ x ∈ A, x ^ 4 = 1 → x ∈ powSub A 2)
    {u : P} (hu : u * u ∈ A) (a : ↥A) :
    ((l3Sqrt h hA u (l3Sqrt h hA u a) : ↥A) : P)
      * ((l3Sqrt h hA u a : ↥A) : P)⁻¹ ∈ powSub A 2 := by
  have h1 := nu_idem_L3 h hA hA4 hu a
  have h2 : ((l3Sqrt h hA u a : ↥A) : P) * ((l3Sqrt h hA u a : ↥A) : P) ∈ powSub A 2 := by
    rw [l3Sqrt_sq h hA u a]
    exact l3Delta_mem_powSub_two h hA u a
  have h3 : (((l3Sqrt h hA u a : ↥A) : P) * ((l3Sqrt h hA u a : ↥A) : P))⁻¹ ∈ powSub A 2 :=
    (powSub A 2).inv_mem h2
  have hmul := (powSub A 2).mul_mem h1 h3
  rwa [show (((l3Sqrt h hA u (l3Sqrt h hA u a) : ↥A) : P)
        * ((l3Sqrt h hA u a : ↥A) : P))
      * (((l3Sqrt h hA u a : ↥A) : P) * ((l3Sqrt h hA u a : ↥A) : P))⁻¹
      = ((l3Sqrt h hA u (l3Sqrt h hA u a) : ↥A) : P)
        * ((l3Sqrt h hA u a : ↥A) : P)⁻¹ from by group] at hmul

/-- **Higman (1963), Lemma 3.**  Let `A` be a normal abelian `X`-subgroup of a Suzuki 2-group and
`C > A` a normal `X`-subgroup covering `A` with `Φ(C) = Φ(A) = A²`; then `A` has exponent at
most `4`.

Proof (Higman pp. 83–84), organised as follows.

* `Φ(C) = A²` gives `C² ≤ A²`, so for `u ∈ C` the conjugation derivation `a ↦ Δ_u(a) = u⁻¹aua⁻¹`
lands in `A²` and `u² ∈ A`.
* **Phase 1.**  The quotient `V = A/A²` is an `𝔽₂`-vector space on which `ξ` acts transitively
  on non-zero vectors.  The square roots `ν_u(a)` of the `Δ_u(a)` (`l3Sqrt`, from
  `Submission.Work.Higman.lemma3_core`) induce endomorphisms `σ u` of `V`, which are additive in
  `u` (`nu_add`), idempotent (`nu_idem_L3` + `A[4] ⊆ A²`) and `ξ`-equivariant (`nu_eqv_L3`).
  Higman's Boolean idempotent family lemma (`boolean_idempotent_family`) then shows
  `σ u ∈ {0, id}`; the kernel of `σ` is exactly `A` by Higman's Lemma 2 (`higman_lemma2`), since
  `σ u = 0` forces `[u, A] ⊆ A⁴` and `u² ∈ A²`.  Hence `|C/A| ≤ 2` and, as `A ≠ C`,
  `C ∖ A = u A` for any `u ∈ C ∖ A`.
* **Phase 2** (`final_step_L3`).  With `C ∖ A = u A`, the endomorphism `a ↦ a·u⁻¹au` of `A` has
  image `FA`, and the subgroup `B` generated by the squares of the elements of `C ∖ A` satisfies
  `B = FA ⊔ ⟨u²⟩` with `u⁴ ∈ FA`.  If `u² ∈ FA` then `(u a₀⁻¹)² = 1` for suitable `a₀`, giving an
  involution of `C ∖ A` (impossible, all involutions lie in `A`); if `u² ∉ FA` then `B/F A` has
  order two, i.e. `|B| = 2|FA|`, which contradicts the homocyclic tower of `ξ`-invariant
  subgroups of `A` (`tower_contra_L3`).

The same statement is also available as `Work.Higman.higman_lemma3_general` in
`Submission.Work.Higman.lemma9_maximal_abelian`; the proof below is independent of it and has a
much smaller dependency footprint. -/
theorem lemma3 {P : Type} [Group P] [Finite P] (h : Work.Higman.IsSuzuki2Grp P) {A C : Subgroup P}
    (hA : Work.Higman.IsXiAbelNormal h A)
    (hCn : C.Normal) (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C) (hAC : A ≤ C)
    (hCA : A ≠ C)
    (hcover : ∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
      A ≤ D → D ≤ C → D = A ∨ D = C)
    (hPhi : Work.Higman.powSub C 2 ⊔ ⁅C, C⁆ = Work.Higman.powSub A 2) :
    ∀ a ∈ A, a ^ 4 = 1 := by
  have hAb : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := hA.abelian
  have hAinv : A.map (h.xi : MulAut P).toMonoidHom = A := hA.map_eq
  have hC2 : powSub C 2 ≤ powSub A 2 := by rw [← hPhi]; exact le_sup_left
  have hC2A : powSub C 2 ≤ A := hC2.trans (powSub_le (n := 2) (by norm_num))
  have hu2Aof : ∀ v ∈ C, v * v ∈ A := fun v hv =>
    hC2A (by rw [← pow_two]; exact pow_mem_powSub hv)
  suffices hgoal : powSub A 4 = ⊥ by
    intro a ha
    have hmem : a ^ 4 ∈ (⊥ : Subgroup P) := by rw [← hgoal]; exact pow_mem_powSub ha
    simpa using Subgroup.mem_bot.mp hmem
  by_contra hne4
  have hAne : A ≠ ⊥ := by
    intro hb
    exact hne4 (by rw [hb]; exact le_antisymm (powSub_le (n := 4) (by norm_num)) bot_le)
  have hOm : omega1 P ≤ A := l3_omega1_le_of_ne_bot h hA hAne
  obtain ⟨e, he1, he2, hkey⟩ := mem_powSub_two_iff h hA
  have he3 : 3 ≤ e := by
    by_contra hlt
    push_neg at hlt
    apply hne4
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨y, hyA, hy⟩ := (mem_powSub_iff hAb).mp hx
    rw [← hy]
    obtain ⟨k, hk⟩ : ∃ k, 4 = 2 ^ e * k := by
      have hd : 2 ^ e ∣ 4 := by
        have h := Nat.pow_dvd_pow 2 (show e ≤ 2 by omega)
        simpa using h
      exact ⟨4 / 2 ^ e, by rw [mul_comm]; exact (Nat.div_mul_cancel hd).symm⟩
    calc y ^ 4 = y ^ (2 ^ e * k) := by rw [← hk]
      _ = (y ^ 2 ^ e) ^ k := by rw [pow_mul]
      _ = 1 := by rw [he1 y hyA, one_pow]
  have hA2 : ∀ x ∈ A, x * x = 1 → x ∈ powSub A 2 :=
    fun x hx hx2 => l3_mem_powSub_two_of_sq_one hkey (by omega) hx hx2
  have hA4 : ∀ x ∈ A, x ^ 4 = 1 → x ∈ powSub A 2 :=
    fun x hx hx4 => l3_mem_powSub_two_of_four_one hkey he3 hx hx4
  obtain ⟨u, huC, huA⟩ : ∃ u ∈ C, u ∉ A := by
    by_contra hc
    push_neg at hc
    exact hCA (le_antisymm hAC fun x hx => hc x hx)
  -- ### Phase 1: the `𝔽₂`-vector space `V = A / A²` and the idempotents `σ u`
  letI hAc : CommGroup ↥A := { (inferInstance : Group ↥A) with
    mul_comm := fun x y => Subtype.ext (hAb x x.2 y y.2) }
  let K : Subgroup ↥A := (powSub A 2).subgroupOf A
  have hKn : K.Normal := Subgroup.normal_of_comm K
  let V := Additive (↥A ⧸ K)
  have hVtwo : ∀ x : V, (2 : ℕ) • x = 0 := by
    intro x
    induction x using QuotientGroup.induction_on with
    | _ a =>
      show (2 : ℕ) • (Additive.ofMul (QuotientGroup.mk a) : V) = 0
      rw [two_nsmul, ← ofMul_mul, ofMul_eq_zero, ← QuotientGroup.mk_mul,
        QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      show ((a : ↥A) : P) * ((a : ↥A) : P) ∈ powSub A 2
      rw [← pow_two]
      exact pow_mem_powSub a.2
  letI hVmod : Module (ZMod 2) V := AddCommGroup.zmodModule (n := 2) (G := V) hVtwo
  haveI hVfintype : Fintype V := Fintype.ofFinite V
  haveI hCfintype : Fintype ↥C := Fintype.ofFinite _
  -- the homomorphism `ν_u : A → A / A²`
  let hσhom : ∀ w : P, ↥A →* (↥A ⧸ K) := fun w =>
    { toFun := fun a => QuotientGroup.mk (l3Sqrt h hA w a)
      map_one' := by
        show QuotientGroup.mk (l3Sqrt h hA w 1) = 1
        rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
        exact l3Sqrt_one h hA hA2 w
      map_mul' := fun a b => by
        show QuotientGroup.mk (l3Sqrt h hA w (a * b))
          = QuotientGroup.mk (l3Sqrt h hA w a) * QuotientGroup.mk (l3Sqrt h hA w b)
        rw [← QuotientGroup.mk_mul, QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf]
        simpa [div_eq_mul_inv] using l3Sqrt_mul h hA hA2 w a b }
  have hσhom_apply : ∀ (w : P) (a : ↥A),
      (hσhom w) a = QuotientGroup.mk (l3Sqrt h hA w a) := fun w a => rfl
  let hσker : ∀ w : P, K ≤ (hσhom w).ker := by
    intro w c hc
    have hc2 : ((c : ↥A) : P) ∈ powSub A 2 := Subgroup.mem_subgroupOf.mp hc
    have hw := l3Sqrt_wd h hA hA2 w (1 : ↥A) (c := ((c : ↥A) : P)) c.2 hc2
    rw [one_mul] at hw
    have hone : ((l3Sqrt h hA w 1 : ↥A) : P) ∈ powSub A 2 := l3Sqrt_one h hA hA2 w
    have hm : ((l3Sqrt h hA w c : ↥A) : P) ∈ powSub A 2 := by
      have hmul := Subgroup.mul_mem (powSub A 2) hw hone
      rwa [show (((l3Sqrt h hA w c : ↥A) : P) * ((l3Sqrt h hA w 1 : ↥A) : P)⁻¹)
          * ((l3Sqrt h hA w 1 : ↥A) : P) = ((l3Sqrt h hA w c : ↥A) : P) from by group] at hmul
    rw [MonoidHom.mem_ker, hσhom_apply w c, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf]
    exact hm
  let σg : ↥C → (↥A ⧸ K) →* (↥A ⧸ K) := fun i =>
    QuotientGroup.lift K (hσhom (i : P)) (hσker (i : P))
  let σ : ↥C → V →ₗ[ZMod 2] V := fun i => (MonoidHom.toAdditive (σg i)).toZModLinearMap 2
  have hσ_apply : ∀ (i : ↥C) (a : ↥A),
      σ i (Additive.ofMul (QuotientGroup.mk a))
        = Additive.ofMul (QuotientGroup.mk (l3Sqrt h hA (i : P) a)) := by
    intro i a
    have h1 : σg i (QuotientGroup.mk a) = QuotientGroup.mk (l3Sqrt h hA (i : P) a) := by
      show (QuotientGroup.lift K (hσhom (i : P)) (hσker (i : P))) (QuotientGroup.mk a) = _
      rw [QuotientGroup.lift_mk' K (hσker (i : P)) a, hσhom_apply]
    rw [show σ i (Additive.ofMul (QuotientGroup.mk a))
        = Additive.ofMul (σg i (QuotientGroup.mk a)) from rfl, h1]
  -- ## `σ` consists of idempotents
  have hσidem : ∀ i : ↥C, (σ i).comp (σ i) = σ i := by
    intro i
    refine LinearMap.ext fun x => ?_
    rw [show x = Additive.ofMul (Additive.toMul x) from (ofMul_toMul x).symm]
    refine QuotientGroup.induction_on (Additive.toMul x) fun a => ?_
    show (σ i) ((σ i) (Additive.ofMul (QuotientGroup.mk a)))
        = (σ i) (Additive.ofMul (QuotientGroup.mk a))
    rw [hσ_apply i a, hσ_apply i (l3Sqrt h hA (i : P) a)]
    congr 1
    rw [QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf]
    simpa [div_eq_mul_inv] using nu_idem_mod h hA hA4 (u := (i : P)) (hu2Aof (i : P) i.2) a
  -- ## `σ` is additive in the group variable
  have hσadd_mul : ∀ i j : ↥C, σ (i * j) = σ i + σ j := by
    intro i j
    refine LinearMap.ext fun x => ?_
    rw [show x = Additive.ofMul (Additive.toMul x) from (ofMul_toMul x).symm]
    refine QuotientGroup.induction_on (Additive.toMul x) fun a => ?_
    show (σ (i * j)) (Additive.ofMul (QuotientGroup.mk a))
        = (σ i + σ j) (Additive.ofMul (QuotientGroup.mk a))
    rw [LinearMap.add_apply, hσ_apply (i * j) a, hσ_apply i a, hσ_apply j a,
      ← ofMul_mul, ← QuotientGroup.mk_mul]
    congr 1
    rw [QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf]
    simpa [div_eq_mul_inv] using nu_add h hA hA2 (i : P) (j : P) a
  have hσadd : ∀ i j : ↥C, ∃ k : ↥C, σ k = σ i + σ j :=
    fun i j => ⟨i * j, hσadd_mul i j⟩
  -- ## the `ξ`-action on `V`
  let ξA : ↥A ≃* ↥A :=
    { toFun := xiSub h hAinv
      invFun := fun a => ⟨h.xi.symm (a : P), symm_mem_of_map_eq h.xi hAinv a.2⟩
      left_inv := fun a => Subtype.ext (by
        show h.xi.symm (h.xi (a : P)) = (a : P)
        rw [MulEquiv.symm_apply_apply])
      right_inv := fun a => Subtype.ext (by
        show h.xi (h.xi.symm (a : P)) = (a : P)
        rw [MulEquiv.apply_symm_apply])
      map_mul' := fun a b => xiSub_mul h hAinv a b }
  have hξA_coe : ∀ a : ↥A, ((ξA a : ↥A) : P) = h.xi (a : P) := fun a => rfl
  have hKmap : K.map ξA.toMonoidHom = K := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      have hy2 : ((y : ↥A) : P) ∈ powSub A 2 := Subgroup.mem_subgroupOf.mp hy
      have hξ := Subgroup.mem_map_of_mem (h.xi : MulAut P).toMonoidHom hy2
      rw [map_powSub h.xi hAinv 2] at hξ
      exact Subgroup.mem_subgroupOf.mpr (by simpa [hξA_coe] using hξ)
    · intro hx
      have hx2 : ((x : ↥A) : P) ∈ powSub A 2 := Subgroup.mem_subgroupOf.mp hx
      have hpre : h.xi.symm ((x : ↥A) : P) ∈ powSub A 2 := by
        have h := symm_mem_of_map_eq h.xi (map_powSub h.xi hAinv 2) hx2
        simpa using h
      have hpreA : h.xi.symm ((x : ↥A) : P) ∈ A :=
        symm_mem_of_map_eq h.xi hAinv (powSub_le (n := 2) (by norm_num) hx2)
      refine ⟨⟨h.xi.symm ((x : ↥A) : P), hpreA⟩, Subgroup.mem_subgroupOf.mpr hpre, ?_⟩
      apply Subtype.ext
      show h.xi (h.xi.symm ((x : ↥A) : P)) = ((x : ↥A) : P)
      rw [MulEquiv.apply_symm_apply]
  let ξQ : (↥A ⧸ K) ≃* (↥A ⧸ K) := QuotientGroup.congr K K ξA hKmap
  let ξV : V ≃ₗ[ZMod 2] V :=
    { MulEquiv.toAdditive ξQ with
      map_smul' := fun c x => ZMod.map_smul (MulEquiv.toAdditive ξQ) c x }
  have hξV_apply : ∀ (a : ↥A), ξV (Additive.ofMul (QuotientGroup.mk a))
      = Additive.ofMul (QuotientGroup.mk (xiSub h hAinv a)) := by
    intro a
    rw [show ξV (Additive.ofMul (QuotientGroup.mk a))
        = Additive.ofMul (ξQ (QuotientGroup.mk a)) from rfl,
      show ξQ (QuotientGroup.mk a) = QuotientGroup.mk (ξA a) from
        QuotientGroup.congr_mk K K ξA hKmap a,
      show QuotientGroup.mk (ξA a) = QuotientGroup.mk (xiSub h hAinv a) from rfl]
  -- ## transitivity of `ξV` on non-zero vectors
  have key : ∀ (k : ℕ) (x y : ↥A),
      (h.xi ^ k) (x : P) * (y : P)⁻¹ ∈ powSub A 2 →
      (ξV ^ k) (Additive.ofMul (QuotientGroup.mk x))
        = Additive.ofMul (QuotientGroup.mk y) := by
    intro k
    induction k with
    | zero =>
      intro x y hk
      show Additive.ofMul (QuotientGroup.mk x) = Additive.ofMul (QuotientGroup.mk y)
      exact congrArg (Additive.ofMul : ↥A ⧸ K → V) (by
        rw [QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf]
        simpa [div_eq_mul_inv] using hk)
    | succ k ih =>
      intro x y hk
      rw [pow_succ]
      show (ξV ^ k) (ξV (Additive.ofMul (QuotientGroup.mk x)))
        = Additive.ofMul (QuotientGroup.mk y)
      rw [hξV_apply]
      refine ih (xiSub h hAinv x) y ?_
      show (h.xi ^ k) (h.xi (x : P)) * (y : P)⁻¹ ∈ powSub A 2
      rw [← MulAut.mul_apply, ← pow_succ]
      exact hk
  have key2 : ∀ (p q : ↥A ⧸ K), p ≠ 1 → q ≠ 1 →
      ∃ k : ℕ, (ξV ^ k) (Additive.ofMul p) = Additive.ofMul q := by
    intro p q hp hq
    induction p using QuotientGroup.induction_on with
    | _ x =>
      induction q using QuotientGroup.induction_on with
      | _ y =>
        have hx : ((x : ↥A) : P) ∉ powSub A 2 := by
          intro hc
          exact hp (by
            rw [QuotientGroup.eq_one_iff]
            exact Subgroup.mem_subgroupOf.mpr hc)
        have hy : ((y : ↥A) : P) ∉ powSub A 2 := by
          intro hc
          exact hq (by
            rw [QuotientGroup.eq_one_iff]
            exact Subgroup.mem_subgroupOf.mpr hc)
        obtain ⟨k, hk⟩ := xi_trans_quot_sq h hA x.2 y.2 hx hy
        exact ⟨k, key k x y hk⟩
  have htrans : ∀ a b : V, a ≠ 0 → b ≠ 0 → ∃ k : ℕ, (ξV ^ k) a = b := by
    intro a b ha hb
    have ha' : (Additive.toMul a) ≠ 1 := by
      intro h1
      refine ha ?_
      rw [show (a : V) = Additive.ofMul (Additive.toMul a) from (ofMul_toMul a).symm,
        h1, ofMul_one]
    have hb' : (Additive.toMul b) ≠ 1 := by
      intro h1
      refine hb ?_
      rw [show (b : V) = Additive.ofMul (Additive.toMul b) from (ofMul_toMul b).symm,
        h1, ofMul_one]
    obtain ⟨k, hk⟩ := key2 (Additive.toMul a) (Additive.toMul b) ha' hb'
    refine ⟨k, ?_⟩
    rw [show a = Additive.ofMul (Additive.toMul a) from (ofMul_toMul a).symm,
      show b = Additive.ofMul (Additive.toMul b) from (ofMul_toMul b).symm]
    exact hk
  -- ## the `ξ`-action on `↥C`
  let τ : ↥C ≃* ↥C :=
    (C.equivMapOfInjective (h.xi : MulAut P).toMonoidHom h.xi.injective).trans
      (MulEquiv.subgroupCongr hCinv)
  have hτ_coe : ∀ i : ↥C, ((τ i : ↥C) : P) = h.xi (i : P) := by
    intro i
    show h.xi (((i : ↥C) : P)) = h.xi ((i : ↥C) : P)
    rfl
  -- ## `σ` is `ξ`-equivariant
  have hσeqv : ∀ (i : ↥C) (v : V), σ (τ i) (ξV v) = ξV (σ i v) := by
    intro i v
    rw [show v = Additive.ofMul (Additive.toMul v) from (ofMul_toMul v).symm]
    refine QuotientGroup.induction_on (Additive.toMul v) fun a => ?_
    show σ (τ i) (ξV (Additive.ofMul (QuotientGroup.mk a)))
        = ξV (σ i (Additive.ofMul (QuotientGroup.mk a)))
    rw [hξV_apply, hσ_apply, hσ_apply, hξV_apply]
    congr 1
    rw [QuotientGroup.eq_iff_div_mem, Subgroup.mem_subgroupOf]
    have hstep := nu_eqv_L3 h hA hAinv hA2 (i : P) a
    simpa [hτ_coe, div_eq_mul_inv] using hstep
  -- ## the Boolean idempotent family: `σ i ∈ {0, id}`
  have hσtriv : ∀ i : ↥C, σ i = 0 ∨ σ i = LinearMap.id :=
    boolean_idempotent_family ξV htrans σ hσidem hσadd ⟨τ.toEquiv, fun i v => hσeqv i v⟩
  -- ## the kernel of `σ` is `A`
  have hker : ∀ i : ↥C, σ i = 0 ↔ (i : P) ∈ A := by
    intro i
    constructor
    · intro h0
      by_contra hiA
      have hν : ∀ a : ↥A, ((l3Sqrt h hA (i : P) a : ↥A) : P) ∈ powSub A 2 := by
        intro a
        have h1 := congrArg (fun f : V →ₗ[ZMod 2] V =>
          f (Additive.ofMul (QuotientGroup.mk a))) h0
        rw [hσ_apply i a, LinearMap.zero_apply, ofMul_eq_zero, QuotientGroup.eq_one_iff] at h1
        exact Subgroup.mem_subgroupOf.mp h1
      have hcom : ∀ a ∈ A, ⁅(i : P), a⁆ ∈ powSub A 4 := by
        intro a ha
        have h4 : ((l3Delta hA.normal hA.abelian (i : P) ⟨a, ha⟩ : ↥A) : P) ∈ powSub A 4 := by
          rw [l3Delta_apply, ← l3Sqrt_sq h hA (i : P) ⟨a, ha⟩]
          have hm : ((l3Sqrt h hA (i : P) ⟨a, ha⟩ : ↥A) : P) ^ 2 ∈ powSub A 4 := by
            have h := pow_mem_powSub (A := powSub A 2) (n := 2) (hν ⟨a, ha⟩)
            rwa [powSub_powSub hAb, show 2 * 2 = 4 from rfl] at h
          rwa [pow_two] at hm
        have hconj : (i : P)
            * (((l3Delta hA.normal hA.abelian (i : P) ⟨a, ha⟩ : ↥A) : P))⁻¹
            * (i : P)⁻¹ = ⁅(i : P), a⁆ := by
          rw [l3Delta_apply, commutatorElement_def]
          group
        rw [← hconj]
        exact (powSub_normal hA.normal 4).conj_mem _
          ((powSub A 4).inv_mem h4) (i : P)
      exact higman_lemma2 h hA hOm hAne hiA ⟨hC2 (pow_mem_powSub i.2), hcom⟩
    · intro hiA
      have hpt : ∀ a : ↥A, σ i (Additive.ofMul (QuotientGroup.mk a)) = 0 := by
        intro a
        rw [hσ_apply i a, ofMul_eq_zero, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
        refine hA2 _ (l3Sqrt h hA (i : P) a).2 ?_
        rw [l3Sqrt_sq h hA (i : P) a]
        show (i : P)⁻¹ * (a : P) * (i : P) * (a : P)⁻¹ = 1
        rw [show (i : P)⁻¹ * (a : P) * (i : P) * (a : P)⁻¹
            = ((i : P)⁻¹ * (a : P)) * ((i : P) * (a : P)⁻¹) from by group,
          hAb (i : P) hiA (a : P)⁻¹ (A.inv_mem a.2)]
        group
      refine LinearMap.ext fun x => ?_
      rw [show x = Additive.ofMul (Additive.toMul x) from (ofMul_toMul x).symm]
      refine QuotientGroup.induction_on (Additive.toMul x) fun a => ?_
      change σ i (Additive.ofMul (QuotientGroup.mk a)) = 0
      rw [hpt a]
  -- ### Conclusion of Phase 1: `C ∖ A = u · A`
  have hsep : ∀ v : P, v ∈ C → v ∉ A → v * u⁻¹ ∈ A := by
    intro v hvC hvA
    have hvuC : v * u⁻¹ ∈ C := C.mul_mem hvC (C.inv_mem huC)
    have hσu : σ ⟨u, huC⟩ ≠ 0 := fun h0 => huA ((hker ⟨u, huC⟩).mp h0)
    have hσv : σ ⟨v, hvC⟩ ≠ 0 := fun h0 => hvA ((hker ⟨v, hvC⟩).mp h0)
    have hu_id : σ ⟨u, huC⟩ = LinearMap.id := by
      rcases hσtriv ⟨u, huC⟩ with h | h
      · exact absurd h hσu
      · exact h
    have hv_id : σ ⟨v, hvC⟩ = LinearMap.id := by
      rcases hσtriv ⟨v, hvC⟩ with h | h
      · exact absurd h hσv
      · exact h
    have h2 : σ ((⟨u, huC⟩ : ↥C)⁻¹) = -σ ⟨u, huC⟩ := by
      have hsum : σ ⟨u, huC⟩ + σ ((⟨u, huC⟩ : ↥C)⁻¹) = 0 := by
        have h := hσadd_mul (⟨u, huC⟩ : ↥C) ((⟨u, huC⟩ : ↥C)⁻¹)
        rw [mul_inv_cancel] at h
        rw [← h]
        exact (hker 1).mpr A.one_mem
      calc σ ((⟨u, huC⟩ : ↥C)⁻¹) = 0 - σ ⟨u, huC⟩ := by
            rw [← hsum]; abel
        _ = -σ ⟨u, huC⟩ := by simp
    have hz : σ ⟨v * u⁻¹, hvuC⟩ = 0 := by
      have h1 : σ ((⟨v, hvC⟩ : ↥C) * (⟨u, huC⟩ : ↥C)⁻¹)
          = σ ⟨v, hvC⟩ + σ ((⟨u, huC⟩ : ↥C)⁻¹) := hσadd_mul _ _
      rw [show (⟨v, hvC⟩ : ↥C) * (⟨u, huC⟩ : ↥C)⁻¹ = ⟨v * u⁻¹, hvuC⟩ from
        Subtype.ext rfl] at h1
      rw [h1, hv_id, h2, hu_id, add_neg_cancel]
    exact (hker ⟨v * u⁻¹, hvuC⟩).mp hz
  exact final_step_L3 h hA hCinv hAC hC2 hOm u huC huA hsep

end Work.Higman.CommAux
