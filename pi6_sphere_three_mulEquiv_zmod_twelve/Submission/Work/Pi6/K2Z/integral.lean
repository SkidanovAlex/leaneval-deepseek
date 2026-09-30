import Mathlib
import Submission.Work.Pi6.Interfaces
import Submission.Work.Pi6.K2Z.fieldHalf
import Submission.Work.Cohomology.KroneckerH
import Submission.Work.Pi6.KronBridge
import Submission.Work.Pi6.EMM2.cupOne
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option autoImplicit false
set_option maxHeartbeats 0

/-!
# `K2Z` — the integral half of `K2ZFacts`

Given the integral homology of a `K(ℤ,2)` range model `X` (free through degree `8`, `ℤ` in even
degrees and `0` in odd degrees — `Work.Pi6.K2Z.fgFromPrimes`), the degree-local universal
coefficient theorem (`kronH`) identifies `H^{2k}(X;ℤ)` with `Hom(H_{2k}(X;ℤ),ℤ) ≅ ℤ` and kills the
odd cohomology.  The class `x ∈ H²(X;ℤ)` is pinned down by the Kronecker pairing with a generator of
`H₂(X;ℤ)` and the multiplicative coefficient reduction to `𝔽_p` (`Work.Pi6.K2Z.redNat`) shows that
all cup powers of `x` are primitive, hence generate `H^{2k}(X;ℤ)`.
-/

open CategoryTheory CategoryTheory.Limits

namespace Work.Pi6.K2Z

noncomputable section

/-- **Homogeneity of the cup power**: `(c • v)^k = c^k • v^k`. -/
theorem cpow_smul {𝕜 : Type} [CommRing 𝕜] {X : Type} [TopologicalSpace X] (c : 𝕜)
    (v : Work.Pi6.Coh 𝕜 X 2) (k : ℕ) :
    Work.Pi6.cpow (c • v) k = c ^ k • Work.Pi6.cpow v k := by
  induction k with
  | zero => simp [Work.Pi6.cpow]
  | succ k ih =>
      have h1 : Work.Pi6.cpow (c • v) (k + 1)
          = Work.Pi6.cup 𝕜 X (2 * k) 2 (Work.Pi6.cpow (c • v) k) (c • v) := rfl
      rw [h1, ih, Work.Pi6.cpow]
      rw [map_smul, map_smul, LinearMap.smul_apply]
      rw [smul_smul, pow_succ']

/-- **Cup powers of a nonzero class in a one-dimensional `H²`**: if `w₀ ≠ 0` has `w₀^k ≠ 0` and
`H²` is one-dimensional then every nonzero class has non-vanishing `k`-th cup power. -/
theorem cpow_ne_zero_of_finrank_one {𝕜 : Type} [Field 𝕜] {X : Type} [TopologicalSpace X] {k : ℕ}
    (h2 : Module.finrank 𝕜 (Work.Pi6.Coh 𝕜 X 2) = 1)
    {w₀ : Work.Pi6.Coh 𝕜 X 2} (hw₀ : w₀ ≠ 0) (hpow : Work.Pi6.cpow w₀ k ≠ 0)
    {v : Work.Pi6.Coh 𝕜 X 2} (hv : v ≠ 0) : Work.Pi6.cpow v k ≠ 0 := by
  obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' w₀ hw₀).mp h2 v
  subst hc
  rw [cpow_smul]
  refine smul_ne_zero ?_ hpow
  exact pow_ne_zero k (fun hc0 => hv (by rw [hc0, zero_smul]))

/-- A nonzero integer with no prime divisor is `± 1`. -/
theorem int_eq_one_or_neg_one_of_prime_free {m : ℤ} (h0 : m ≠ 0)
    (h : ∀ p : ℕ, p.Prime → ¬ ((p : ℤ) ∣ m)) : m = 1 ∨ m = -1 := by
  have hnat : m.natAbs = 1 := by
    by_contra hne
    obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hne
    have hpm : (p : ℤ) ∣ m :=
      (Int.natAbs_dvd_natAbs (a := (p : ℤ)) (b := m)).mp (by simpa using hpdvd)
    exact h p hp hpm
  have hsq : m ^ 2 = (1 : ℤ) ^ 2 := (Int.natAbs_eq_iff_sq_eq).mp (by rw [hnat]; rfl)
  simpa using hsq

/-- The first cup power is the class itself. -/
theorem cpow_one {R : Type} [CommRing R] {X : Type} [TopologicalSpace X]
    (v : Work.Pi6.Coh R X 2) : Work.Pi6.cpow v 1 = v := by
  show (Work.Pi6.cup R X 0 2) (Work.Pi6.one R X) v = v
  have h1 : (Work.Pi6.cup R X 0 2) (Work.Pi6.one R X) v = (Nat.zero_add 2).symm ▸ v :=
    Work.Cohomology.cupH'_one_left R (TopCat.toSSet.obj (TopCat.of X)) 2 v
  rw [h1]

/-- The Kronecker pairing `Hⁿ(X;R) →ₗ (Hₙ(X;R) →ₗ R)` of the interface
(`Work.Pi6.kronL`). -/
abbrev kron (R : Type) [CommRing R] (X : Type) [TopologicalSpace X] (n : ℕ) :=
  Work.Pi6.kronL R X n

/-- The Kronecker pairing vanishes on `0`. -/
theorem kron_zero (R : Type) [CommRing R] (X : Type) [TopologicalSpace X] (n : ℕ)
    (c : Work.Pi6.HR R X n) : kron R X n 0 c = 0 := by
  rw [map_zero, LinearMap.zero_apply]

/-- The coefficient reduction to `𝔽_p`, as produced by `Work.Pi6.K2Z.coeffChange`/`redNat`. -/
structure RedData (p : ℕ) [Fact p.Prime] (X : Type) [TopologicalSpace X] where
  redCoh : ∀ n : ℕ, Work.Pi6.Coh ℤ X n →ₗ[ℤ] Work.Pi6.Coh (ZMod p) X n
  redHom : ∀ n : ℕ, Work.Pi6.HR ℤ X n →ₗ[ℤ] Work.Pi6.HR (ZMod p) X n
  mul : ∀ (n m : ℕ) (x : Work.Pi6.Coh ℤ X n) (y : Work.Pi6.Coh ℤ X m),
    redCoh (n + m) ((Work.Pi6.cup ℤ X n m) x y) =
      (Work.Pi6.cup (ZMod p) X n m) (redCoh n x) (redCoh m y)
  pair : ∀ (n : ℕ) (x : Work.Pi6.Coh ℤ X n) (c : Work.Pi6.HR ℤ X n),
    kron (ZMod p) X n (redCoh n x) (redHom n c) = ((kron ℤ X n x c : ℤ) : ZMod p)

/-- The multiplicative coefficient reduction in degree `2*k` agrees with the cup power. -/
theorem RedData.pow {p : ℕ} [Fact p.Prime] {X : Type} [TopologicalSpace X] (D : RedData p X)
    (x : Work.Pi6.Coh ℤ X 2) {k : ℕ} (hk : 1 ≤ k) :
    D.redCoh (2 * k) (Work.Pi6.cpow x k) = Work.Pi6.cpow (D.redCoh 2 x) k := by
  induction k with
  | zero => omega
  | succ k ih =>
      rcases Nat.eq_zero_or_pos k with h | h
      · subst h
        rw [cpow_one x, cpow_one (D.redCoh 2 x)]
      · have ih' := ih (by omega)
        calc D.redCoh (2 * (k + 1)) (Work.Pi6.cpow x (k + 1))
            = D.redCoh (2 * k + 2)
                ((Work.Pi6.cup ℤ X (2 * k) 2) (Work.Pi6.cpow x k) x) := rfl
          _ = (Work.Pi6.cup (ZMod p) X (2 * k) 2) (D.redCoh (2 * k) (Work.Pi6.cpow x k))
                (D.redCoh 2 x) := D.mul (2 * k) 2 (Work.Pi6.cpow x k) x
          _ = (Work.Pi6.cup (ZMod p) X (2 * k) 2)
                (Work.Pi6.cpow (D.redCoh 2 x) k) (D.redCoh 2 x) := by rw [ih']
          _ = Work.Pi6.cpow (D.redCoh 2 x) (k + 1) := rfl


/-- **The integral half of `K2ZFacts`**, given the integral homology of the range model
(`Work.Pi6.K2Z.fgFromPrimes`), the degree-local universal coefficient theorem
(`Work.Pi6.K2Z.kronH_bij`) and the multiplicative coefficient reduction to `𝔽_p`
(`Work.Pi6.K2Z.redNat`). -/
theorem integralPart_of {X : Type} [TopologicalSpace X] (x₀ : X) (N : ℕ) (hN : 10 ≤ N)
    (hX : Work.Serre.IsEMSpaceUpTo ℤ 2 (by norm_num) N X x₀)
    (hfgP : (∀ k : ℕ, k ≤ 4 → Nonempty (Work.Pi6.HR ℤ X (2 * k) ≅ ModuleCat.of ℤ ℤ)) ∧
      (∀ k : ℕ, k ≤ 4 → Subsingleton (Work.Pi6.HR ℤ X (2 * k + 1))) ∧
      (∀ n : ℕ, n ≤ 8 → Module.Free ℤ (Work.Pi6.HR ℤ X n)))
    (hkron : ∀ (n : ℕ), (∀ k : ℕ, k < n → Module.Free ℤ (Work.Pi6.HR ℤ X k)) →
      Function.Bijective (Work.Cohomology.kronH ℤ (TopCat.toSSet.obj (TopCat.of X)) n))
    (hfield : ∀ (𝕜 : Type) [Field 𝕜], ∃ w : Work.Pi6.Coh 𝕜 X 2, ∀ k : ℕ, k ≤ 4 →
        Work.Pi6.cpow w k ≠ 0 ∧ Module.finrank 𝕜 (Work.Pi6.Coh 𝕜 X (2 * k)) = 1 ∧
          Subsingleton (Work.Pi6.Coh 𝕜 X (2 * k + 1)))
    (hred : ∀ (p : ℕ) [Fact p.Prime], RedData p X) :
    ∃ x : Work.Pi6.Coh ℤ X 2,
      (∀ k : ℕ, k ≤ 4 → ∀ a : Work.Pi6.Coh ℤ X (2 * k),
        ∃! n : ℤ, a = n • Work.Pi6.cpow x k) ∧
      (∀ k : ℕ, k ≤ 4 → Subsingleton (Work.Pi6.Coh ℤ X (2 * k + 1))) := by
  obtain ⟨hH2, hHodd, hfree⟩ := hfgP
  -- Kronecker isomorphisms in the needed range
  have hkronIso : ∀ n : ℕ, (∀ k < n, Module.Free ℤ (Work.Pi6.HR ℤ X k)) →
      Nonempty (↥(Work.Pi6.Coh ℤ X n) ≃ₗ[ℤ] (↥(Work.Pi6.HR ℤ X n) →ₗ[ℤ] ℤ)) :=
    fun n hn => ⟨LinearEquiv.ofBijective
      (Work.Cohomology.kronH ℤ (TopCat.toSSet.obj (TopCat.of X)) n) (hkron n hn)⟩
  -- the distinguished class `x`, pinned by the Kronecker pairing
  obtain ⟨eH2⟩ := hH2 1 (by norm_num)
  let e2 : ↥(Work.Pi6.HR ℤ X 2) ≃ₗ[ℤ] ℤ := eH2.toLinearEquiv
  let kron2 : ↥(Work.Pi6.Coh ℤ X 2) ≃ₗ[ℤ] (↥(Work.Pi6.HR ℤ X 2) →ₗ[ℤ] ℤ) :=
    LinearEquiv.ofBijective (kron ℤ X 2)
      ((Work.Pi6.kronL_bijective_iff ℤ X 2).mpr (hkron 2 (fun k hk => hfree k (by omega))))
  let x : Work.Pi6.Coh ℤ X 2 := kron2.symm (e2.toLinearMap)
  have hx : ∀ c : ↥(Work.Pi6.HR ℤ X 2), kron2 x c = e2 c :=
    fun c => congrArg (fun f => f c) (LinearEquiv.apply_symm_apply kron2 (e2.toLinearMap))
  -- the reduction is nonzero on `x`
  have hredx : ∀ (p : ℕ) [Fact p.Prime], (hred p).redCoh 2 x ≠ 0 := by
    intro p hp
    have h1 := (hred p).pair 2 x (e2.symm (1 : ℤ))
    have h2 : (kron ℤ X 2 x (e2.symm (1 : ℤ)) : ℤ) = 1 := by
      show (kron ℤ X 2 x (e2.symm (1 : ℤ))) = 1
      rw [show kron ℤ X 2 x (e2.symm (1 : ℤ)) = kron2 x (e2.symm (1 : ℤ)) from rfl, hx,
        LinearEquiv.apply_symm_apply]
    have h1' : kron (ZMod p) X 2 ((hred p).redCoh 2 x)
        ((hred p).redHom 2 (e2.symm (1 : ℤ))) = 1 := by
      rw [h1, h2]
      norm_num
    intro hzero
    have hne : (1 : ZMod p) ≠ 0 := by
      intro h
      have h1 : ((1 : ℕ) : ZMod p) = 0 := by simpa using h
      exact hp.out.ne_one (Nat.dvd_one.mp ((ZMod.natCast_eq_zero_iff 1 p).mp h1))
    have hfun := congrArg (fun y => kron (ZMod p) X 2 y) hzero
    rw [map_zero (kron (ZMod p) X 2)] at hfun
    rw [hfun] at h1'
    rw [LinearMap.zero_apply] at h1'
    exact hne (by simpa using h1'.symm)
  -- the reduction is nonzero on the unit
  have hredone : ∀ (p : ℕ) [Fact p.Prime], (hred p).redCoh 0 (Work.Pi6.one ℤ X) ≠ 0 := by
    intro p hp hzero
    have hx1 : (Work.Pi6.cup ℤ X 2 0) x (Work.Pi6.one ℤ X) = x :=
      Work.Cohomology.cupH'_one_right ℤ (TopCat.toSSet.obj (TopCat.of X)) 2 x
    have h2 := (hred p).mul 2 0 x (Work.Pi6.one ℤ X)
    have hR : (Work.Pi6.cup (ZMod p) X 2 0) ((hred p).redCoh 2 x)
        ((hred p).redCoh 0 (Work.Pi6.one ℤ X)) = 0 :=
      (congrArg (fun t => (Work.Pi6.cup (ZMod p) X 2 0) ((hred p).redCoh 2 x) t) hzero).trans
        (map_zero _)
    rw [hR] at h2
    have h3 : (hred p).redCoh 2 x = 0 := by
      have h4 := h2
      rw [hx1] at h4
      exact h4
    exact hredx p h3
  -- the reduction of the `k`-th cup power is nonzero
  have hredpow : ∀ (p : ℕ) [Fact p.Prime] (k : ℕ), 1 ≤ k → k ≤ 4 →
      (hred p).redCoh (2 * k) (Work.Pi6.cpow x k) ≠ 0 := by
    intro p hp k hk1 hk4
    rw [(hred p).pow x hk1]
    obtain ⟨w, hw⟩ := hfield (ZMod p)
    exact cpow_ne_zero_of_finrank_one (k := k) (hw 1 (by norm_num)).2.1
      (fun hw0 => (hw 1 (by norm_num)).1 (by rw [hw0, cpow_one (0 : Work.Pi6.Coh (ZMod p) X 2)]))
      ((hw k hk4).1) (hredx p)
  -- primality of the cup powers
  have hprim : ∀ (k : ℕ) (hk4 : k ≤ 4) (e : ↥(Work.Pi6.Coh ℤ X (2 * k)) ≃ₗ[ℤ] ℤ),
      e (Work.Pi6.cpow x k) = 1 ∨ e (Work.Pi6.cpow x k) = -1 := by
    intro k hk4 e
    rcases Nat.eq_zero_or_pos k with hk0 | hk1
    · -- `k = 0`: use the nonzero reduction of the unit
      subst hk0
      refine int_eq_one_or_neg_one_of_prime_free ?_ ?_
      · intro h0
        have h1 : Work.Pi6.one ℤ X = 0 := e.map_eq_zero_iff.mp h0
        exact hredone 2 (by rw [h1, LinearMap.map_zero])
      · intro p hp hdvd
        haveI : Fact p.Prime := ⟨hp⟩
        obtain ⟨m', hm'⟩ := hdvd
        have hxk : Work.Pi6.cpow x 0 = (p : ℤ) • e.symm m' := by
          apply e.injective
          rw [map_zsmul, LinearEquiv.apply_symm_apply, zsmul_eq_mul]
          exact hm'
        rw [show Work.Pi6.cpow x 0 = Work.Pi6.one ℤ X from rfl] at hxk
        have hz := hredone p
        rw [hxk, map_zsmul] at hz
        refine hz ?_
        rw [← Int.cast_smul_eq_zsmul (ZMod p)]
        push_cast
        rw [show ((p : ℕ) : ZMod p) = 0 from ZMod.natCast_self p, zero_smul]
    · refine int_eq_one_or_neg_one_of_prime_free ?_ ?_
      · intro h0
        have hz := hredpow 2 k hk1 hk4
        rw [show Work.Pi6.cpow x k = (0 : Work.Pi6.Coh ℤ X (2 * k)) from e.map_eq_zero_iff.mp h0,
          map_zero] at hz
        exact hz rfl
      · intro p hp hdvd
        obtain ⟨m', hm'⟩ := hdvd
        have hxk : Work.Pi6.cpow x k = (p : ℤ) • e.symm m' := by
          apply e.injective
          rw [map_zsmul, LinearEquiv.apply_symm_apply, zsmul_eq_mul]
          exact hm'
        haveI : Fact p.Prime := ⟨hp⟩
        have hz := hredpow p k hk1 hk4
        rw [hxk, map_zsmul] at hz
        refine hz ?_
        rw [← Int.cast_smul_eq_zsmul (ZMod p)]
        push_cast
        rw [show ((p : ℕ) : ZMod p) = 0 from ZMod.natCast_self p, zero_smul]
  refine ⟨x, ?_, ?_⟩
  · intro k hk4 a
    obtain ⟨eH⟩ := hH2 k hk4
    let e : ↥(Work.Pi6.Coh ℤ X (2 * k)) ≃ₗ[ℤ] ℤ :=
      (LinearEquiv.ofBijective (kron ℤ X (2 * k))
        ((Work.Pi6.kronL_bijective_iff ℤ X (2 * k)).mpr
          (hkron (2 * k) (fun j hj => hfree j (by omega))))).trans
        ((LinearEquiv.dualMap eH.toLinearEquiv).symm.trans (LinearMap.ringLmapEquivSelf ℤ ℤ ℤ))
    have hkey := hprim k hk4 e
    have hε0 : e (Work.Pi6.cpow x k) ≠ 0 := by
      rcases hkey with h | h <;> rw [h] <;> norm_num
    have hε : e (Work.Pi6.cpow x k) * e (Work.Pi6.cpow x k) = 1 := by
      rcases hkey with h | h <;> rw [h] <;> norm_num
    refine ⟨e a * e (Work.Pi6.cpow x k), ?_, ?_⟩
    · apply e.injective
      rw [map_zsmul]
      change e a = e a * e (Work.Pi6.cpow x k) * e (Work.Pi6.cpow x k)
      rw [mul_assoc, hε, mul_one]
    · intro n hn
      have h1 : n * e (Work.Pi6.cpow x k) = e a := by
        have h2 := congrArg e hn.symm
        rw [map_zsmul] at h2
        change n * e (Work.Pi6.cpow x k) = e a at h2
        exact h2
      calc n = n * (e (Work.Pi6.cpow x k) * e (Work.Pi6.cpow x k)) := by rw [hε, mul_one]
        _ = n * e (Work.Pi6.cpow x k) * e (Work.Pi6.cpow x k) := by rw [mul_assoc]
        _ = e a * e (Work.Pi6.cpow x k) := by rw [h1]
  · intro k hk4
    obtain ⟨e⟩ := hkronIso (2 * k + 1) (fun j hj => hfree j (by omega))
    haveI hHoddk : Subsingleton (Work.Pi6.HR ℤ X (2 * k + 1)) := hHodd k hk4
    haveI : Subsingleton (↥(Work.Pi6.HR ℤ X (2 * k + 1)) →ₗ[ℤ] ℤ) :=
      ⟨fun f g => by
        ext c
        rw [show c = 0 from Subsingleton.elim c 0, map_zero, map_zero]⟩
    exact ⟨fun u v => e.injective (Subsingleton.elim _ _)⟩

end

end Work.Pi6.K2Z
