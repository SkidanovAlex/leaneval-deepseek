import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.local_detect_h_pgroup
import Submission.Work.SSGRoute.ext_one_iso_divisible_cohomology
import Submission.Work.SSGRoute.SSGStage.archimedeanLocalDictionary
import Submission.Work.SSGRoute.extH_natCard_smul_eq_zero
import Submission.Work.SSGRoute.local_pTorsion_card
import Submission.Work.SSGRoute.e6_util
import Submission.Work.SSGRoute.homRep
import Submission.Work.SSGRoute.local_ext_h1_bridge
import Submission.Work.SSGRoute.localAlgebraMapUnits_self
import Submission.Work.SSGRoute.local_duality_ext_in
import Submission.Work.SSGRoute.PT.pt_pairing_ext
import Submission.Work.SSGRoute.ext_localUnits_pTorsion
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! Guidance from the project lead (the requester):

Lead design (Claude) 10-05 03:15 (_lead_design/flags_0230/p2/NOTE.md): p = 2 pieces for G1⁺ (involution pairing χ∘ι∘yonedaPair replaces E7Arch.pairArchFamily at p = 2).
-/

namespace Work.SSGRoute.PT

open CategoryTheory SSGRoute.PTExt

noncomputable section

variable {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K] [Algebra k K]
  [FiniteDimensional k K] [IsGalois k K]

/-- A place that is not finite is `ofInfinite` of an archimedean place. -/
theorem exists_ofInfinite_eq_of_ne_ofFinite (w : NK.GlobalCFT.Place K)
    (hw : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      w ≠ NK.GlobalCFT.Place.ofFinite q) :
    ∃ u : NumberField.InfinitePlace K, w = NK.GlobalCFT.Place.ofInfinite u := by
  rcases w with u | q
  · exact ⟨u, rfl⟩
  · exact absurd rfl (hw q)

/-- **`decompK` of an infinite place is the stabiliser.** -/
theorem decompK_ofInfinite_eq (u : NumberField.InfinitePlace K) :
    decompK (k := k) (NK.GlobalCFT.Place.ofInfinite u) = MulAction.stabilizer (K ≃ₐ[k] K) u :=
  Work.SSGRoute.SSGStage.decompK_ofInfinite_eq_stabilizer (k := k) (K := K) u

/-- **The decomposition group of a ramified infinite place has order two.** -/
theorem natCard_decompK_eq_two_of_ne_bot (w : NK.GlobalCFT.Place K)
    (hw : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      w ≠ NK.GlobalCFT.Place.ofFinite q)
    (hD : decompK (k := k) w ≠ ⊥) :
    Nat.card (decompK (k := k) w) = 2 := by
  obtain ⟨u, rfl⟩ := exists_ofInfinite_eq_of_ne_ofFinite w hw
  rw [decompK_ofInfinite_eq]
  have hstab : MulAction.stabilizer (K ≃ₐ[k] K) u ≠ ⊥ := by
    rw [← decompK_ofInfinite_eq (k := k) (K := K) u]; exact hD
  have hram : NumberField.InfinitePlace.IsRamified k u := fun hunr =>
    hstab ((NumberField.InfinitePlace.isUnramified_iff_stabilizer_eq_bot).mp hunr)
  exact (NumberField.InfinitePlace.not_isUnramified_iff_card_stabilizer_eq_two).mp hram

/-- `decompK w` is a `2`-group when `w` is infinite with nontrivial decomposition group. -/
theorem isPGroup_two_decompK (w : NK.GlobalCFT.Place K)
    (hw : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      w ≠ NK.GlobalCFT.Place.ofFinite q)
    (hD : decompK (k := k) w ≠ ⊥) :
    IsPGroup 2 (decompK (k := k) w) :=
  IsPGroup.of_card (n := 1) (by rw [natCard_decompK_eq_two_of_ne_bot (k := k) w hw hD, pow_one])

/-- At a ramified infinite place the local field is `ℂ`. -/
theorem isComplex_of_place_ne_bot (w : NK.GlobalCFT.Place K)
    (hw : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      w ≠ NK.GlobalCFT.Place.ofFinite q)
    (hD : decompK (k := k) w ≠ ⊥) :
    ∃ u : NumberField.InfinitePlace K, w = NK.GlobalCFT.Place.ofInfinite u ∧ u.IsComplex := by
  obtain ⟨u, rfl⟩ := exists_ofInfinite_eq_of_ne_ofFinite w hw
  exact ⟨u, rfl,
    Work.SSGRoute.SSGStage.isComplex_of_decompK_ofInfinite_ne_bot (k := k) (K := K) hD⟩

/-! ## The pairing at a complex archimedean place

Notation for the rest of the file: `X := res M` (the module restricted to `D_w`) and `A := K_wˣ`.
Both are `Rep Coeff (decompK w)`-objects, `V = Ext¹_D(X, A)` is the source and `W = H¹(D, X)` the
target of the Yoneda pairing `yonedaPair`.

Two facts do all the work:

* (clause 2, all `M`) right detection at the archimedean place comes from the E7b `p`-group node
  `Work.SSGRoute.local_detect_h_pgroup` (with the tower `D_w = D_w`, `ι = 𝟙`), which is available
  because `|D_w| = 2` and `A` is divisible there;
* the cardinality `|V| = |W|` is obtained by applying right detection *twice*: once for `X`, and
  once for the dual module `homRep X A`, whose `Ext¹`-source is `W` (dictionary) and whose
  `H¹`-target is `V` (dictionary + the canonical double duality `X ≈ homRep (homRep X A) A`).

Then clause 1 is finite duality on top of clause 2. -/

section Pairing

variable {M : Rep.{0} Coeff (K ≃ₐ[k] K)} [Finite M] {p : ℕ} [Fact p.Prime]

/-- The source module `res M` of the pairing. -/
abbrev resM (M : Rep.{0} Coeff (K ≃ₐ[k] K)) (w : NK.GlobalCFT.Place K) :
    Rep.{0} Coeff (decompK (k := k) w) := Rep.res (decompK (k := k) w).subtype M

/-- The coefficient module `K_wˣ` of the pairing. -/
abbrev localU (w : NK.GlobalCFT.Place K) : Rep.{0} Coeff (decompK (k := k) w) :=
  localUnitsK (k := k) w

/-- **In a field of characteristic `≠ 2` the `2`-torsion of the additive group of units is
`{0, -1}`.** -/
theorem exists_two_torsion_units (F : Type) [Field F] (h2 : (2 : F) ≠ 0) :
    ∃ a₀ : Additive Fˣ, a₀ ≠ 0 ∧ (2 : ℕ) • a₀ = 0 ∧
      ∀ a : Additive Fˣ, (2 : ℕ) • a = 0 → a = 0 ∨ a = a₀ := by
  refine ⟨Additive.ofMul (-1 : Fˣ), ?_, ?_, ?_⟩
  · intro h
    have h' : (-1 : Fˣ) = 1 := by
      have h0 := congrArg (fun x : Additive Fˣ => Additive.toMul x) h
      simpa using h0
    have h2' : (-1 : F) = 1 := by
      simpa using congrArg (fun x : Fˣ => (x : F)) h'
    have hzero : (2 : F) = 0 := by linear_combination (-1 : F) * h2'
    exact h2 hzero
  · rw [← ofMul_pow, neg_one_sq, ofMul_one]
  · intro a ha
    obtain ⟨v, hv⟩ := (Additive.ofMul (α := Fˣ)).surjective a
    subst hv
    have hv2 : (v : F) * (v : F) = 1 := by
      have h1 : v ^ 2 = (1 : Fˣ) := by
        have h2' : Additive.ofMul (v ^ 2) = (0 : Additive Fˣ) := by
          rw [ofMul_pow]
          exact ha
        exact ofMul_eq_zero.mp h2'
      have h3 := congrArg (fun x : Fˣ => (x : F)) h1
      simpa [Units.val_pow_eq_pow_val, pow_two] using h3
    rcases (mul_self_eq_one_iff).mp hv2 with h1 | h1
    · left
      rw [← ofMul_one]
      exact congrArg Additive.ofMul (Units.ext (by simpa using h1))
    · right
      exact congrArg Additive.ofMul (Units.ext (by simpa using h1))

/-- **The `2`-torsion of the local units at a complex archimedean place is `{0, -1}`.** -/
theorem exists_two_torsion_negOneU (w : NK.GlobalCFT.Place K)
    (hw : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      w ≠ NK.GlobalCFT.Place.ofFinite q)
    (hD : decompK (k := k) w ≠ ⊥) :
    ∃ a₀ : (localU (k := k) (K := K) w).V, a₀ ≠ 0 ∧ (2 : ℕ) • a₀ = 0 ∧
      ∀ a : (localU (k := k) (K := K) w).V, (2 : ℕ) • a = 0 → a = 0 ∨ a = a₀ := by
  obtain ⟨u, rfl, hu⟩ := isComplex_of_place_ne_bot (k := k) w hw hD
  have h2F : (2 : u.Completion) ≠ 0 := by
    have h2C : (2 : ℂ) ≠ 0 := by norm_num
    intro h
    refine h2C ?_
    have h1 := congrArg
      (fun x => NumberField.InfinitePlace.Completion.ringEquivComplexOfIsComplex hu x) h
    simpa only [map_ofNat, map_zero] using h1
  obtain ⟨a₀, ha₀, ha₀2, hgen⟩ := exists_two_torsion_units u.Completion h2F
  exact ⟨a₀, ha₀, ha₀2, hgen⟩

/-- **The local units at a complex archimedean place are divisible.** -/
theorem localU_divisible (w : NK.GlobalCFT.Place K)
    (hw : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      w ≠ NK.GlobalCFT.Place.ofFinite q)
    (hD : decompK (k := k) w ≠ ⊥) :
    ∀ (n : ℕ), 0 < n → ∀ y : (localU (k := k) w).V, ∃ x : (localU (k := k) w).V, n • x = y := by
  obtain ⟨u, rfl, hu⟩ := isComplex_of_place_ne_bot (k := k) w hw hD
  exact Work.SSGRoute.SSGStage.localUnitsK_divisible_of_isComplex (k := k) (K := K) hu

/-- **`LiesOver w w`** (the place lies over itself), used to instantiate the E7b tower at
`L = K`, `w' = w`. -/
theorem place_liesOver_self' (w : NK.GlobalCFT.Place K) : NK.GlobalCFT.Place.LiesOver w w := by
  rcases w with u | q
  · refine NK.GlobalCFT.Place.liesOver_ofInfinite ?_
    exact (NK.GlobalCFT.Norm.liesOver_iff_comap_eq u u).mpr (NumberField.InfinitePlace.comap_id u)
  · refine NK.GlobalCFT.Place.liesOver_ofFinite ?_
    exact (NK.GlobalCFT.Norm.liesOver_iff_under_eq q.asIdeal q.asIdeal).mpr (by
      rw [Ideal.under_def, Algebra.algebraMap_self, Ideal.comap_id])

/-- **The level pairing with `f = id` and the identity of the *restricted* coefficient module is
the Yoneda pairing** (the shape produced by right detection at the base level, where the
coefficient morphism is `𝟙 (Rep.res (MonoidHom.id G) A)`). -/
theorem levelPair_id_res {G : Type} [Group G] {M A : Rep.{0} Coeff G} {r s : ℕ}
    (x : Abelian.Ext.{0} M A r) (h : extH M s) :
    levelPair (MonoidHom.id G) (𝟙 (Rep.res (MonoidHom.id G) A)) x h = yonedaPair x h := by
  have hι : (𝟙 (Rep.res (MonoidHom.id G) A) : Rep.res (MonoidHom.id G) A ⟶ A)
      = (𝟙 A : A ⟶ A) := rfl
  rw [hι]
  exact Work.SSGRoute.levelPair_id x h

/-- **Right detection at the complex archimedean place: clause 2**, for every finite `p`-torsion
module over `D_w`.  This is the E7b `p`-group node `Work.SSGRoute.local_detect_h_pgroup` at the
tower `f = id`, `ι = 𝟙`, `L = K`, `w' = w`, converted to the `yonedaPair` form by `levelPair_id`. -/
theorem clause_two_rep (w : NK.GlobalCFT.Place K)
    (hw : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      w ≠ NK.GlobalCFT.Place.ofFinite q)
    (hD : decompK (k := k) w ≠ ⊥)
    (N : Rep.{0} Coeff (decompK (k := k) w)) [Finite N]
    (hN : ∀ n : N, p • n = 0) (hp : p = 2) :
    ∀ h : extH N 1, h ≠ 0 →
      ∃ y : Abelian.Ext N (localU (k := k) (K := K) w) 1, yonedaPair y h ≠ 0 := by
  subst hp
  intro h hh
  have hLies : NK.GlobalCFT.Place.LiesOver w w := place_liesOver_self' (K := K) w
  have hp' : 2 ∣ Nat.card (MulAction.stabilizer (K ≃ₐ[k] K) w) := by
    have h2 : Nat.card (MulAction.stabilizer (K ≃ₐ[k] K) w)
        = Nat.card (decompK (k := k) w) := rfl
    rw [h2, natCard_decompK_eq_two_of_ne_bot (k := k) w hw hD]
  have hrd := Work.SSGRoute.local_detect_h_pgroup (p := 2) (k := k) (K := K) (w := w)
    (isPGroup_two_decompK (k := k) w hw hD) N (fun n => hN n) K
    w hLies (MonoidHom.id _)
    (fun σ => by
      rw [show galRes k K K = MonoidHom.id (K ≃ₐ[k] K) from AlgEquiv.restrictNormalHom_id k K]
      rfl)
    (𝟙 _)
    (fun u => by
      rw [Work.SSGRoute.localAlgebraMapUnits_self K w hLies u]
      rfl)
    hp'
  obtain ⟨y, hy⟩ := hrd h hh
  exact ⟨y, fun h0 => hy (by rw [levelPair_id_res, h0])⟩

/-- Clause 2 of the target, for the module `res M` of the pairing. -/
theorem clause_two (w : NK.GlobalCFT.Place K)
    (hw : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      w ≠ NK.GlobalCFT.Place.ofFinite q)
    (hD : decompK (k := k) w ≠ ⊥)
    (M : Rep.{0} Coeff (K ≃ₐ[k] K)) [Finite M]
    (hM : ∀ m : M, p • m = 0) (hp : p = 2) :
    ∀ h : extH (resM (k := k) (K := K) M w) 1, h ≠ 0 →
      ∃ y : Abelian.Ext (resM (k := k) (K := K) M w) (localU (k := k) (K := K) w) 1,
        yonedaPair y h ≠ 0 :=
  clause_two_rep (k := k) (K := K) w hw hD (resM (k := k) (K := K) M w)
    (fun n => hM n) hp

end Pairing

/-! ## General auxiliary facts -/

section General

/-- **Bezout vanishing of `Ext¹_G(ℤ, A)`**: if `A` is `p`-torsion and `p` is coprime to the order
of the finite group `G`, then `H¹(G, A) = 0`. -/
theorem subsingleton_extH_one_of_coprime {G : Type} [Group G] [Fintype G] (p : ℕ) [Fact p.Prime]
    (A : Rep.{0} Coeff G) (hA : ∀ a : A, p • a = 0) (hcop : Nat.Coprime p (Nat.card G)) :
    Subsingleton (extH A 1) := by
  have hbez : (p : ℤ) * (Nat.gcdA p (Nat.card G))
      + (Nat.card G : ℤ) * (Nat.gcdB p (Nat.card G)) = 1 := by
    have h := Nat.gcd_eq_gcd_ab p (Nat.card G)
    rw [hcop.gcd_eq_one, Nat.cast_one] at h
    linarith [h]
  have hzero : ∀ y : extH A 1, p • y = 0 → y = 0 := by
    intro y hy
    have hDy : Nat.card G • y = 0 := extH_natCard_smul_eq_zero A (n := 1) (by norm_num) y
    have hy' : (p : ℤ) • y = 0 := by
      rw [Nat.cast_smul_eq_nsmul ℤ p]; exact hy
    have hDy' : (Nat.card G : ℤ) • y = 0 := by
      rw [Nat.cast_smul_eq_nsmul ℤ (Nat.card G)]; exact hDy
    calc y = (1 : ℤ) • y := (one_smul _ _).symm
      _ = ((p : ℤ) * (Nat.gcdA p (Nat.card G))
            + (Nat.card G : ℤ) * (Nat.gcdB p (Nat.card G))) • y := by rw [hbez]
      _ = (Nat.gcdA p (Nat.card G)) • ((p : ℤ) • y)
            + (Nat.gcdB p (Nat.card G)) • ((Nat.card G : ℤ) • y) := by
            rw [add_smul, mul_smul, mul_smul,
              smul_comm (p : ℤ) (Nat.gcdA p (Nat.card G)) y,
              smul_comm (Nat.card G : ℤ) (Nat.gcdB p (Nat.card G)) y]
      _ = 0 := by rw [hy', hDy']; simp
  exact ⟨fun x y => by
    rw [hzero x (ext_nsmul_p_torsion p hA x), hzero y (ext_nsmul_p_torsion p hA y)]⟩

/-- `Hom_ℤ(X, A)` is `2`-torsion as soon as `X` is. -/
theorem homRep_two_torsion {G : Type} [Group G] {X A : Rep.{0} Coeff G}
    (hX : ∀ x : X.V, (2 : ℕ) • x = 0) (f : Work.SSGRoute.homRep X A) : (2 : ℕ) • f = 0 := by
  change (2 : ℕ) • (show X.V →ₗ[Coeff] A.V from f) = 0
  rw [two_nsmul]
  refine LinearMap.ext (fun x => ?_)
  rw [LinearMap.add_apply, ← two_nsmul,
    ← map_nsmul (show X.V →ₗ[Coeff] A.V from f) 2 x, hX x, map_zero, LinearMap.zero_apply]

end General

/-! ### `𝔽₂`-duality of hom modules -/

section Basic

variable {A : Type} [AddCommGroup A] [Module Coeff A] {a₀ : A}

theorem int_smul_two (h2 : (2 : ℕ) • a₀ = 0) : (2 : ℤ) • a₀ = 0 := by
  rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) from rfl, Nat.cast_smul_eq_nsmul ℤ 2]
  exact h2

theorem add_self_eq_zero (h2 : (2 : ℕ) • a₀ = 0) : a₀ + a₀ = 0 := by
  rw [← two_nsmul]; exact h2

theorem neg_eq_self (h2 : (2 : ℕ) • a₀ = 0) : -a₀ = a₀ :=
  (neg_eq_iff_add_eq_zero).mpr (add_self_eq_zero h2)

theorem smul_a₀_of_dvd (h2 : (2 : ℕ) • a₀ = 0) {k : ℤ} (hk : (2 : ℤ) ∣ k) :
    k • a₀ = 0 := by
  obtain ⟨m, hm⟩ := hk
  rw [hm, mul_comm, mul_zsmul, int_smul_two h2, smul_zero]

theorem smul_a₀_of_not_dvd (h2 : (2 : ℕ) • a₀ = 0) {k : ℤ} (hk : ¬ (2 : ℤ) ∣ k) :
    k • a₀ = a₀ := by
  have hmod : k % 2 = 1 := by
    rcases Int.emod_two_eq_zero_or_one k with h | h
    · exact absurd ⟨k / 2, by omega⟩ hk
    · exact h
  calc k • a₀ = (2 * (k / 2) + k % 2) • a₀ := by rw [Int.mul_ediv_add_emod]
    _ = (2 * (k / 2)) • a₀ + (k % 2) • a₀ := by rw [add_zsmul]
    _ = (k / 2) • ((2 : ℤ) • a₀) + (k % 2) • a₀ := by rw [mul_comm, mul_zsmul]
    _ = a₀ := by rw [int_smul_two h2, smul_zero, zero_add, hmod, one_zsmul]

theorem zmodTwo_eq_one {r : ZMod 2} (h : r ≠ 0) : r = 1 := by
  have hv : r.val < 2 := ZMod.val_lt r
  have hne : r.val ≠ 0 := by
    intro h0
    exact h (by rw [← ZMod.natCast_zmod_val r, h0]; rfl)
  have h1 : r.val = 1 := by omega
  rw [← ZMod.natCast_zmod_val r, h1]; rfl

theorem zsmul_one_eq (k : ℤ) : k • (1 : ZMod 2) = (k : ZMod 2) := by
  rw [← Int.cast_smul_eq_zsmul (ZMod 2) k 1, smul_eq_mul, mul_one]

variable {Y : Type} [AddCommGroup Y] [Module Coeff Y]

/-- The "characteristic function" of the nonzero element of the `2`-torsion. -/
def ind (a₀ a : A) : ZMod 2 := by
  classical
  exact if a = 0 then 0 else 1

theorem ind_zero (a₀ : A) : ind a₀ (0 : A) = 0 := by
  classical
  unfold ind
  rw [if_pos rfl]

theorem ind_self (hne : a₀ ≠ 0) : ind a₀ a₀ = 1 := by
  classical
  unfold ind
  rw [if_neg hne]

theorem ind_add (h2 : (2 : ℕ) • a₀ = 0) (hne : a₀ ≠ 0)
    (hgen : ∀ a : A, (2 : ℕ) • a = 0 → a = 0 ∨ a = a₀) {a b : A}
    (ha : (2 : ℕ) • a = 0) (hb : (2 : ℕ) • b = 0) :
    ind a₀ (a + b) = ind a₀ a + ind a₀ b := by
  classical
  rcases hgen a ha with rfl | rfl
  · rcases hgen b hb with rfl | rfl
    · rw [zero_add, ind_zero, add_zero]
    · rw [zero_add, ind_self hne, ind_zero, zero_add]
  · rcases hgen b hb with rfl | rfl
    · rw [add_zero, ind_self hne, ind_zero, add_zero]
    · rw [add_self_eq_zero h2, ind_zero, ind_self hne]
      decide

theorem ind_eq_zero_iff (hne : a₀ ≠ 0)
    (hgen : ∀ a : A, (2 : ℕ) • a = 0 → a = 0 ∨ a = a₀) {a : A}
    (ha : (2 : ℕ) • a = 0) : ind a₀ a = 0 ↔ a = 0 := by
  classical
  rcases hgen a ha with h | h
  · rw [h, ind_zero]
    exact ⟨fun _ => rfl, fun _ => rfl⟩
  · subst h
    rw [ind_self hne]
    exact ⟨fun h0 => absurd h0 one_ne_zero, fun h0 => absurd h0 hne⟩

/-- **The key bijection**: when the `2`-torsion of `A` is `{0, a₀}` and `Y` is `2`-torsion,
`Coeff`-linear maps `Y → A` are the same as additive characters `Y → 𝔽₂`. -/
def homEquiv (hY : ∀ y : Y, (2 : ℕ) • y = 0) (h2 : (2 : ℕ) • a₀ = 0) (hne : a₀ ≠ 0)
    (hgen : ∀ a : A, (2 : ℕ) • a = 0 → a = 0 ∨ a = a₀) :
    (Y →ₗ[Coeff] A) ≃ (Y →+ ZMod 2) where
  toFun f :=
    { toFun := fun y => ind a₀ (f y)
      map_zero' := by rw [map_zero]; exact ind_zero a₀
      map_add' := fun y y' => by
        rw [map_add]
        exact ind_add h2 hne hgen (by rw [← map_nsmul f 2 y, hY y, map_zero])
          (by rw [← map_nsmul f 2 y', hY y', map_zero]) }
  invFun φ :=
    { toFun := fun y => if φ y = 0 then 0 else a₀
      map_add' := fun y y' => by
        classical
        rw [map_add]
        rcases eq_or_ne (φ y) 0 with h | h
        · rcases eq_or_ne (φ y') 0 with h' | h'
          · rw [h, h', add_zero, if_pos rfl, add_zero]
          · rw [h, zmodTwo_eq_one h', zero_add, if_pos rfl, if_neg one_ne_zero, zero_add]
        · rw [zmodTwo_eq_one h]
          rcases eq_or_ne (φ y') 0 with h' | h'
          · rw [h', add_zero, if_pos rfl, if_neg one_ne_zero, add_zero]
          · rw [zmodTwo_eq_one h', show (1 : ZMod 2) + 1 = 0 from by decide,
              if_pos rfl, if_neg one_ne_zero, add_self_eq_zero h2]
      map_smul' := fun c y => by
        classical
        obtain ⟨k⟩ := c
        rw [show ({ down := k } : Coeff) = ((k : ℤ) : Coeff) from rfl, RingHom.id_apply]
        rw [Int.cast_smul_eq_zsmul Coeff k y,
          Int.cast_smul_eq_zsmul Coeff k (if φ y = 0 then 0 else a₀)]
        rw [AddMonoidHom.map_zsmul]
        rcases eq_or_ne (φ y) 0 with h | h
        · rw [h]
          simp
        · have h1 : φ y = 1 := zmodTwo_eq_one h
          rw [h1, if_neg one_ne_zero]
          by_cases hk : (2 : ℤ) ∣ k
          · have hk0 : k • (1 : ZMod 2) = 0 := by
              rw [zsmul_one_eq, ZMod.intCast_zmod_eq_zero_iff_dvd k 2]
              exact hk
            rw [hk0, if_pos rfl, smul_a₀_of_dvd h2 hk]
          · have hk0 : ¬ (k • (1 : ZMod 2) = 0) := by
              rw [zsmul_one_eq]
              intro hc
              exact hk ((ZMod.intCast_zmod_eq_zero_iff_dvd k 2).mp hc)
            rw [if_neg hk0, smul_a₀_of_not_dvd h2 hk] }
  left_inv f := by
    ext y
    classical
    change (if ind a₀ (f y) = 0 then 0 else a₀) = f y
    rcases hgen (f y) (by rw [← map_nsmul f 2 y, hY y, map_zero]) with h | h
    · rw [h, ind_zero, if_pos rfl]
    · rw [h, ind_self hne, if_neg one_ne_zero]
  right_inv φ := by
    ext y
    classical
    change ind a₀ (if φ y = 0 then 0 else a₀) = φ y
    rcases eq_or_ne (φ y) 0 with h | h
    · rw [if_pos h, ind_zero, h]
    · rw [if_neg h, ind_self hne, zmodTwo_eq_one h]

/-- The `𝔽₂`-dual of a finite `2`-torsion module has the same cardinality. -/
theorem natCard_addMonoidHom_zmodTwo [Finite Y] (hY : ∀ y : Y, (2 : ℕ) • y = 0) :
    Nat.card (Y →+ ZMod 2) = Nat.card Y := by
  letI : Module (ZMod 2) Y := AddCommGroup.zmodModule hY
  have e : (Y →+ ZMod 2) ≃ (Y →ₗ[ZMod 2] ZMod 2) :=
    { toFun := fun φ =>
        { toFun := φ
          map_add' := φ.map_add'
          map_smul' := fun c y => by
            rw [RingHom.id_apply]
            have h1 : c • (φ y) = c.val • (φ y) := by
              rw [← Nat.cast_smul_eq_nsmul (R := ZMod 2) c.val (φ y), ZMod.natCast_zmod_val c]
            rw [h1]
            show φ (c.val • y) = c.val • φ y
            rw [map_nsmul] }
      invFun := fun ψ => ψ.toAddMonoidHom
      left_inv := fun φ => by ext y; rfl
      right_inv := fun ψ => by ext y; rfl }
  rw [Nat.card_congr e]
  haveI : Finite (Y →ₗ[ZMod 2] ZMod 2) :=
    Finite.of_injective (fun f : Y →ₗ[ZMod 2] ZMod 2 => (f : Y → ZMod 2))
      DFunLike.coe_injective
  haveI : Module.Finite (ZMod 2) (Y →ₗ[ZMod 2] ZMod 2) := Module.Finite.of_finite
  haveI : Module.Finite (ZMod 2) Y := Module.Finite.of_finite
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Y →ₗ[ZMod 2] ZMod 2),
    Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Y)]
  congr 1
  exact Subspace.dual_finrank_eq

/-- **Cardinality of the hom module**: if the `2`-torsion of `A` is `{0, a₀}` and `Y` is a
finite `2`-torsion module, then `Hom(Y, A)` has the same cardinality as `Y`. -/
theorem natCard_linearMap_eq (hY : ∀ y : Y, (2 : ℕ) • y = 0) (h2 : (2 : ℕ) • a₀ = 0)
    (hne : a₀ ≠ 0) (hgen : ∀ a : A, (2 : ℕ) • a = 0 → a = 0 ∨ a = a₀) [Finite Y] :
    Nat.card (Y →ₗ[Coeff] A) = Nat.card Y := by
  rw [Nat.card_congr (homEquiv hY h2 hne hgen)]
  exact natCard_addMonoidHom_zmodTwo hY

/-- **Separation**: a nonzero `2`-torsion element is detected by a `Coeff`-linear map to `A`. -/
theorem exists_linearMap_apply_ne_zero (hY : ∀ y : Y, (2 : ℕ) • y = 0)
    (h2 : (2 : ℕ) • a₀ = 0) (hne : a₀ ≠ 0)
    (hgen : ∀ a : A, (2 : ℕ) • a = 0 → a = 0 ∨ a = a₀) {x : Y} (hx : x ≠ 0) :
    ∃ f : Y →ₗ[Coeff] A, f x ≠ 0 := by
  classical
  letI : Module (ZMod 2) Y := AddCommGroup.zmodModule hY
  haveI : Module.Free (ZMod 2) Y := Module.Free.of_divisionRing (ZMod 2) Y
  obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one (ZMod 2) hx
  refine ⟨(homEquiv hY h2 hne hgen).symm (φ.toAddMonoidHom), ?_⟩
  have hval : ((homEquiv hY h2 hne hgen).symm (φ.toAddMonoidHom)) x
      = (if φ x = 0 then 0 else a₀) := rfl
  rw [hval, hφ, if_neg one_ne_zero]
  exact hne

end Basic

/-- `extHMap f 𝟙` is `extRes f`. -/
theorem extHMap_one_eq_extRes {G H : Type} [Group G] [Group H] (f : H →* G)
    (M : Rep.{0} Coeff G) (y : extH M 1) :
    extHMap f (𝟙 (Rep.res f M)) y = extRes f y := by
  have h1 : (Abelian.Ext.mk₀ (𝟙 (unitRep H))).comp
      ((extRes f y).comp (Abelian.Ext.mk₀ (𝟙 (Rep.res f M))) (add_zero 1)) (zero_add 1)
      = (extRes f y).comp (Abelian.Ext.mk₀ (𝟙 (Rep.res f M))) (add_zero 1) :=
    Abelian.Ext.mk₀_id_comp _
  rw [show extHMap f (𝟙 (Rep.res f M)) y = (Abelian.Ext.mk₀ (𝟙 (unitRep H))).comp
      ((extRes f y).comp (Abelian.Ext.mk₀ (𝟙 (Rep.res f M))) (add_zero 1)) (zero_add 1) from rfl,
    h1]
  exact Abelian.Ext.comp_mk₀_id _

/-- The restriction `extHMap f 𝟙` along a bijective `f` is surjective. -/
theorem extHMap_one_surjective {G H : Type} [Group G] [Group H] (f : H →* G)
    (hf : Function.Bijective f) (M : Rep.{0} Coeff G) :
    Function.Surjective (fun y : extH M 1 => extHMap f (𝟙 (Rep.res f M)) y) := by
  intro z
  let e : H ≃* G := MulEquiv.ofBijective f hf
  have hsurj : Function.Surjective
      (fun y : extH M 1 => (Work.SSGRoute.LPBC.extResEquiv e (unitRep G) M 1) y) :=
    (Work.SSGRoute.LPBC.extResEquiv e (unitRep G) M 1).surjective
  obtain ⟨y, hy⟩ := hsurj z
  refine ⟨y, ?_⟩
  show extHMap f (𝟙 (Rep.res f M)) y = z
  have h1 : (Work.SSGRoute.LPBC.extResEquiv e (unitRep G) M 1) y = z := hy
  have h2 : (Work.SSGRoute.LPBC.extResEquiv e (unitRep G) M 1) y
      = extHMap f (𝟙 (Rep.res f M)) y := by
    rw [extHMap_one_eq_extRes, Work.SSGRoute.LPBC.extResEquiv_apply]
    rfl
  exact h2.symm.trans h1

/-- The stabilizer of an infinite place is the decomposition subgroup. -/
theorem stabilizer_ofInfinite_eq_decompositionSubgroup {k L : Type} [Field k] [NumberField k]
    [Field L] [NumberField L] [Algebra k L] (v : NumberField.InfinitePlace L) :
    MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofInfinite v)
      = NK.GlobalCFTdeep.decompositionSubgroup (K := k) (L := L)
          (NK.GlobalCFT.Place.ofInfinite v) := by
  refine Subgroup.ext (fun σ => ?_)
  rfl

/-- The stabilizer of an infinite place has order at most two. -/
theorem natCard_stabilizer_ofInfinite_le_two (k L : Type) [Field k] [NumberField k]
    [Field L] [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (v : NumberField.InfinitePlace L) :
    Nat.card ↥(MulAction.stabilizer (L ≃ₐ[k] L) (NK.GlobalCFT.Place.ofInfinite v)) ≤ 2 := by
  rw [stabilizer_ofInfinite_eq_decompositionSubgroup (k := k) v]
  exact Work.SSGRoute.natCard_decompositionSubgroup_ofInfinite_le_two k L v

/-- The stabilizer `Stab_{Gal(L/k)}(w')` has order at most two when `w'` lies over an infinite
place. -/
theorem natCard_stabilizer_le_two_of_liesOver {k K L : Type} [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    [Field L] [NumberField L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional k L] [IsGalois k L]
    (w : NK.GlobalCFT.Place K)
    (hw : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      w ≠ NK.GlobalCFT.Place.ofFinite q)
    (w' : NK.GlobalCFT.Place L) (hw' : NK.GlobalCFT.Place.LiesOver w' w) :
    Nat.card ↥(MulAction.stabilizer (L ≃ₐ[k] L) w') ≤ 2 := by
  obtain ⟨u, rfl⟩ := exists_ofInfinite_eq_of_ne_ofFinite (K := K) w hw
  rcases w' with v | q
  · exact natCard_stabilizer_ofInfinite_le_two k L v
  · exfalso
    rcases (NK.GlobalCFT.Place.liesOver_iff _ _).mp hw' with
      ⟨a, b, h1, h2, _⟩ | ⟨q', Q', h1, h2, _⟩
    · exact absurd h1 (by intro hh; cases hh)
    · exact absurd h2 (by intro hh; cases hh)


/-- **Clause 1 at a complex archimedean place over a real place, `p = 2`.** -/
theorem clause_one_two {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (w : NK.GlobalCFT.Place K)
    (hw : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      w ≠ NK.GlobalCFT.Place.ofFinite q)
    (hD : decompK (k := k) w ≠ ⊥)
    (M : Rep.{0} Coeff (K ≃ₐ[k] K)) [Finite M] (hM : ∀ m : M, (2 : ℕ) • m = 0) :
    ∀ y : Abelian.Ext (Rep.res (decompK (k := k) w).subtype M) (localUnitsK (k := k) w) 1,
      y ≠ 0 → ∃ h : extH (Rep.res (decompK (k := k) w).subtype M) 1,
        yonedaPair y h ≠ 0 := by
  intro y hy
  by_contra hcon
  have hcon' : ∀ h : extH (Rep.res (decompK (k := k) w).subtype M) 1, yonedaPair y h = 0 := by
    intro h
    by_contra h0
    exact hcon ⟨h, h0⟩
  obtain ⟨u, rfl, hu⟩ := isComplex_of_place_ne_bot (k := k) w hw hD
  have hζ : IsPrimitiveRoot (-1 : K) 2 := IsPrimitiveRoot.neg_one 0 (by norm_num)
  have hdet : y = 0 := by
    refine Work.SSGRoute.local_duality_ext_detect_levels 2 k K (-1) hζ M (fun m => hM m)
      (NK.GlobalCFT.Place.ofInfinite u) y ?_
    intro L _ _ _ _ _ _ _ w' hw' f hf ι hι h
    have hsurj : Function.Surjective f :=
      Work.SSGRoute.decompK_restrict_surjective k K _ L w' hw' f hf
    have hle : Nat.card ↥(MulAction.stabilizer (L ≃ₐ[k] L) w') ≤ 2 :=
      natCard_stabilizer_le_two_of_liesOver (k := k) (K := K) (L := L) _ hw w' hw'
    have hcardD : Nat.card ↥(decompK (k := k) (NK.GlobalCFT.Place.ofInfinite u)) = 2 :=
      natCard_decompK_eq_two_of_ne_bot (k := k) _ hw hD
    have hge : 2 ≤ Nat.card ↥(MulAction.stabilizer (L ≃ₐ[k] L) w') := by
      have := Nat.card_le_card_of_surjective f hsurj
      rwa [hcardD] at this
    have hcard : Nat.card ↥(MulAction.stabilizer (L ≃ₐ[k] L) w') = 2 := le_antisymm hle hge
    have hinj : Function.Injective f := by
      have hsplit : Nat.card ↥(MulAction.stabilizer (L ≃ₐ[k] L) w')
          = Nat.card ↥(f.range) * Nat.card ↥(f.ker) := by
        rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (f.ker)]
        rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv]
      have hrange : Nat.card ↥(f.range) = 2 := by
        have htop : f.range = ⊤ := MonoidHom.range_eq_top.mpr hsurj
        rw [htop, Subgroup.card_top, hcardD]
      have hker : Nat.card ↥(f.ker) = 1 := by
        rw [hcard, hrange] at hsplit
        omega
      have hbot : f.ker = ⊥ := by
        rw [← Subgroup.card_eq_one]
        exact hker
      exact (MonoidHom.ker_eq_bot_iff f).mp hbot
    obtain ⟨h₀, hh₀⟩ := extHMap_one_surjective f ⟨hinj, hsurj⟩
      (Rep.res (decompK (k := k) (NK.GlobalCFT.Place.ofInfinite u)).subtype M) h
    rw [← hh₀]
    rw [Work.SSGRoute.levelPair_extHMap f ι y h₀]
    rw [hcon' h₀]
    exact extHMap_zero f ι
  exact hy hdet



/-- `Hom_ℤ(X,A)` is `p`-torsion as soon as `X` is. -/
theorem homRep_nsmul_eq_zero {G : Type} [Group G] {X A : Rep.{0} Coeff G} (p : ℕ)
    (hX : ∀ x : X.V, p • x = 0) (f : Work.SSGRoute.homRep X A) : p • f = 0 := by
  change p • (show X.V →ₗ[Coeff] A.V from f) = 0
  refine LinearMap.ext (fun x => ?_)
  show p • ((show X.V →ₗ[Coeff] A.V from f) x) = 0
  rw [← map_nsmul (show X.V →ₗ[Coeff] A.V from f) p x, hX x, map_zero]

/-- **Clause 1 for odd `p`** (vacuous). -/
theorem clause_one_odd {k K : Type} [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (p : ℕ) [Fact p.Prime] (hp2 : p ≠ 2)
    (w : NK.GlobalCFT.Place K)
    (hw : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      w ≠ NK.GlobalCFT.Place.ofFinite q)
    (hD : decompK (k := k) w ≠ ⊥)
    (M : Rep.{0} Coeff (K ≃ₐ[k] K)) [Finite M] (hM : ∀ m : M, p • m = 0) :
    Subsingleton (Abelian.Ext (Rep.res (decompK (k := k) w).subtype M) (localUnitsK (k := k) w) 1) ∧
      Subsingleton (extH (Rep.res (decompK (k := k) w).subtype M) 1) := by
  have hcard2 : Nat.card ↥(decompK (k := k) w) = 2 :=
    natCard_decompK_eq_two_of_ne_bot (k := k) w hw hD
  have hcop : Nat.Coprime p (Nat.card ↥(decompK (k := k) w)) := by
    rw [hcard2]
    exact (Fact.out : p.Prime).coprime_iff_not_dvd.mpr (fun hdiv =>
      hp2 ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) Nat.prime_two).mp hdiv))
  haveI : Fintype ↥(decompK (k := k) w) := Fintype.ofFinite _
  refine ⟨?_, ?_⟩
  · obtain ⟨e⟩ := Work.SSGRoute.ext_one_iso_divisible_cohomology (decompK (k := k) w)
      (Rep.res (decompK (k := k) w).subtype M) (localUnitsK (k := k) w)
      (localU_divisible (k := k) w hw hD)
    have hN : Subsingleton (extH (Work.SSGRoute.homRep (Rep.res (decompK (k := k) w).subtype M)
        (localUnitsK (k := k) w)) 1) :=
      subsingleton_extH_one_of_coprime p _
        (fun f => homRep_nsmul_eq_zero (X := Rep.res (decompK (k := k) w).subtype M) p
          (fun m => hM m) f) hcop
    exact ⟨fun x y => e.injective (Subsingleton.elim (e x) (e y))⟩
  · exact subsingleton_extH_one_of_coprime p _ (fun m => hM m) hcop

/-- Perfectness of the archimedean Yoneda pairing at a complex place over a real place (the
`ℤ/2` case).

`w` is an infinite place of `K` with `D_w ≠ ⊥`, so `D_w ≅ ℤ/2` and `K_w = ℂ`.  `M` is a finite
`p`-torsion `Gal(K/k)`-module.  Then the Yoneda pairing
`Ext¹_{D_w}(res M, K_wˣ) × H¹(D_w, res M) → H²(D_w, K_wˣ) ≅ ℤ/2`
is non-degenerate on both sides.

Route.  Finite cyclic group of order 2 acting on `ℂˣ`.
* Tate cohomology: `Ĥ⁰(D, ℂˣ) = ℝˣ/ℝ_{>0} = ℤ/2` and `Ĥ¹ = 0` (Hilbert 90).
* Free cover `0 → R → F → M → 0`: `Ext¹_D(M, ℂˣ) = coker(Hom_D(F, ℂˣ) → Hom_D(R, ℂˣ))`.
* Cup product with the generator of `Ĥ²(D, ℤ) = ℤ/2` (periodicity) identifies the pairing with the
  finite-group Tate duality `Ĥ⁻¹(D, Hom(M,ℚ/ℤ)) × Ĥ⁰(D, M) → ℚ/ℤ`.  That is perfect for finite `D`.
* For odd `p` both sides are `0`.
* About 400–700 lines.  No global input is needed.
Use `D_w ≠ ⊥`: when `D_w = ⊥` (a real place of `K`) the pairing at level `K` is not perfect, and one
must pass to a level where `w` becomes complex.  At `p = 2` in the route `ζ₄ ∈ K`, so every infinite
place of `K` is complex. -/
theorem archYoneda_perfect (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k] [Field K]
    [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (M : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite M] (hM : ∀ m : M, p • m = 0)
    (w : NK.GlobalCFT.Place K)
    (hw : ∀ q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      w ≠ NK.GlobalCFT.Place.ofFinite q)
    (hD : SSGRoute.PTExt.decompK (k := k) w ≠ ⊥) :
    (∀ y : CategoryTheory.Abelian.Ext (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype M)
        (SSGRoute.PTExt.localUnitsK (k := k) w) 1, y ≠ 0 →
      ∃ h : SSGRoute.PTExt.extH (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype M) 1,
        SSGRoute.PTExt.yonedaPair y h ≠ 0) ∧
    (∀ h : SSGRoute.PTExt.extH (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype M) 1, h ≠ 0 →
      ∃ y : CategoryTheory.Abelian.Ext (Rep.res (SSGRoute.PTExt.decompK (k := k) w).subtype M)
          (SSGRoute.PTExt.localUnitsK (k := k) w) 1,
        SSGRoute.PTExt.yonedaPair y h ≠ 0) := by
  by_cases hp2 : p = 2
  · subst hp2
    refine ⟨clause_one_two (k := k) (K := K) w hw hD M hM, ?_⟩
    exact clause_two (k := k) (K := K) w hw hD M hM rfl
  · obtain ⟨hV, hW⟩ := clause_one_odd (k := k) (K := K) p hp2 w hw hD M hM
    exact ⟨fun y hy => absurd (Subsingleton.elim y 0) hy,
      fun h hh => absurd (Subsingleton.elim h 0) hh⟩

end

end Work.SSGRoute.PT
