import Mathlib
import Submission.Work.HP.MMDefs
import Submission.Work.HP.Lat.detLAux
import Submission.Work.HP.Lat.prim_bezout
import Submission.Work.HP.Lat.detL_basis_gram
import Submission.Work.HP.NA.VeroAux
import Submission.Work.HP.GM.detL_index
import Submission.Work.HP.FM3.detL_latOrth_free
import Submission.Work.HP.GM.gcdMinors2_veronese_natAbs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
noncomputable section

open Finset

namespace Work.HP

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Elementary lemmas on `dotZ`, `latMod`, `latOrth` -/

/-- Membership in `latMod c Q`: the pairing with `c` is divisible by `Q`. -/
lemma mem_latMod_iff {c y : ι → ℤ} {Q : ℕ} : y ∈ latMod c Q ↔ (Q : ℤ) ∣ dotZ y c := by
  rw [latMod, Submodule.mem_comap, Fintype.linearCombination_apply, dotZ,
    Submodule.mem_span_singleton]
  constructor
  · rintro ⟨a, ha⟩
    exact ⟨a, by simpa [smul_eq_mul, mul_comm] using ha.symm⟩
  · rintro ⟨a, ha⟩
    exact ⟨a, by simpa [smul_eq_mul, mul_comm] using ha.symm⟩

/-- The pairing of a "coordinate vector" with `c`. -/
lemma dotZ_single (a : ι) (c : ι → ℤ) :
    dotZ (fun k => if k = a then (1 : ℤ) else 0) c = c a := by
  rw [dotZ, Finset.sum_eq_single a]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_univ a) h

/-- `dotZ` is additive in its first argument over a finite sum. -/
lemma dotZ_finset_sum {κ : Type*} (s : Finset κ) (f : κ → ι → ℤ) (b : ι → ℤ) :
    dotZ (∑ k ∈ s, f k) b = ∑ k ∈ s, dotZ (f k) b := by
  simp only [dotZ, Finset.sum_apply, Finset.sum_mul]
  exact Finset.sum_comm

/-! ## The two facts about `gcdMinors2 u v` and the functional `⟨v, ·⟩` -/

/-- **Fact A.**  On the lattice `latOrth u` (for `u` primitive), the functional `⟨v, ·⟩` takes
values divisible by the gcd of the `2 × 2` minors of `(u, v)`. -/
theorem gcdMinors2_dvd_dotZ_of_mem_latOrth {u v y : ι → ℤ} (hu : IsPrim u)
    (hy : y ∈ latOrth u) : gcdMinors2 u v ∣ dotZ y v := by
  classical
  obtain ⟨t, ht⟩ := Lat.prim_bezout u hu
  have hy0 : dotZ y u = 0 := mem_latOrth.mp hy
  have hminor : ∀ i j : ι, gcdMinors2 u v ∣ u i * v j - u j * v i :=
    fun i j => Finset.gcd_dvd (Finset.mem_univ (i, j))
  have hui : ∀ i : ι, gcdMinors2 u v ∣ u i * dotZ y v := by
    intro i
    have h2 : gcdMinors2 u v ∣ ∑ j, ((u i * v j - u j * v i)) * y j :=
      Finset.dvd_sum fun j _ => dvd_mul_of_dvd_left (hminor i j) (y j)
    have h3 : ∑ j, ((u i * v j - u j * v i)) * y j = u i * dotZ y v - v i * dotZ y u := by
      simp only [dotZ]
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    rw [h3, hy0, mul_zero, sub_zero] at h2
    exact h2
  have h4 : ∑ i, t i * (u i * dotZ y v) = dotZ y v := by
    have h5 : ∑ i, t i * (u i * dotZ y v) = (∑ i, t i * u i) * dotZ y v := by
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h5, ht, one_mul]
  rw [← h4]
  exact Finset.dvd_sum fun i _ => dvd_mul_of_dvd_right (hui i) (t i)

/-- **Fact C.**  The gcd of the `2 × 2` minors is realised by `⟨v, ·⟩` on `latOrth u`. -/
theorem exists_mem_latOrth_dotZ_eq_gcdMinors2 (u v : ι → ℤ) :
    ∃ y ∈ latOrth u, dotZ y v = gcdMinors2 u v := by
  classical
  obtain ⟨c, hc⟩ := gcd_sum (fun ij : ι × ι => u ij.1 * v ij.2 - u ij.2 * v ij.1)
  have hgc : Finset.univ.gcd (fun ij : ι × ι => u ij.1 * v ij.2 - u ij.2 * v ij.1)
      = gcdMinors2 u v := rfl
  rw [hgc] at hc
  set w : ι × ι → (ι → ℤ) := fun ij =>
    u ij.2 • (fun k => if k = ij.1 then (1 : ℤ) else 0)
      + (-(u ij.1)) • (fun k => if k = ij.2 then (1 : ℤ) else 0) with hw
  have hwu : ∀ ij, dotZ (w ij) u = 0 := by
    intro ij
    simp only [hw, dotZ_add, dotZ_smul, dotZ_single]
    ring
  have hwv : ∀ ij, dotZ (w ij) v = -(u ij.1 * v ij.2 - u ij.2 * v ij.1) := by
    intro ij
    simp only [hw, dotZ_add, dotZ_smul, dotZ_single]
    ring
  refine ⟨∑ ij, (-(c ij)) • w ij, ?_, ?_⟩
  · rw [mem_latOrth]
    show dotZ (∑ ij, (-(c ij)) • w ij) u = 0
    rw [dotZ_finset_sum]
    exact Finset.sum_eq_zero fun ij _ => by rw [dotZ_smul, hwu ij, mul_zero]
  · show dotZ (∑ ij, (-(c ij)) • w ij) v = gcdMinors2 u v
    rw [dotZ_finset_sum]
    have hsum : ∑ ij, dotZ ((-(c ij)) • w ij) v
        = ∑ ij, (-(c ij)) * (-(u ij.1 * v ij.2 - u ij.2 * v ij.1)) :=
      Finset.sum_congr rfl fun ij _ => by rw [dotZ_smul, hwv ij]
    rw [hsum, ← hc]
    exact Finset.sum_congr rfl fun ij _ => by ring

/-! ## The linear map `Λ_u → ℤ/Q`, its kernel and its range -/

/-- The linear map `a ↦ ⟨v, a⟩ mod Q` on the lattice `latOrth u`. -/
def phiMix (u v : ι → ℤ) (Q : ℕ) : latOrth u →ₗ[ℤ] ZMod Q where
  toFun x := ((dotZ x.1 v : ℤ) : ZMod Q)
  map_add' x y := by
    simp only [Submodule.coe_add, dotZ_add, Int.cast_add]
  map_smul' m x := by
    show ((dotZ (m • x.1) v : ℤ) : ZMod Q) = m • ((dotZ x.1 v : ℤ) : ZMod Q)
    rw [dotZ_smul, Int.cast_mul, zsmul_eq_mul]

@[simp] lemma phiMix_apply (u v : ι → ℤ) (Q : ℕ) (x : latOrth u) :
    phiMix u v Q x = ((dotZ x.1 v : ℤ) : ZMod Q) := rfl

/-- The kernel of `phiMix` is exactly `latOrth u ⊓ latMod v Q`. -/
theorem phiMix_ker (u v : ι → ℤ) (Q : ℕ) :
    (phiMix u v Q).ker = (latOrth u ⊓ latMod v Q).comap (latOrth u).subtype := by
  ext x
  rw [LinearMap.mem_ker, Submodule.mem_comap, Submodule.mem_inf]
  constructor
  · intro h
    refine ⟨x.2, ?_⟩
    rw [mem_latMod_iff]
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (dotZ x.1 v) Q).mp h
  · rintro ⟨-, h⟩
    rw [mem_latMod_iff] at h
    exact (ZMod.intCast_zmod_eq_zero_iff_dvd (dotZ x.1 v) Q).mpr h

/-- The range of `phiMix u v Q` is generated by the gcd of the `2 × 2` minors of `(u, v)`. -/
theorem phiMix_range (u v : ι → ℤ) (Q : ℕ) (hu : IsPrim u) :
    (phiMix u v Q).range = Submodule.span ℤ {((gcdMinors2 u v : ℤ) : ZMod Q)} := by
  refine le_antisymm ?_ ?_
  · rintro z ⟨x, rfl⟩
    rw [Submodule.mem_span_singleton]
    obtain ⟨k, hk⟩ := gcdMinors2_dvd_dotZ_of_mem_latOrth (u := u) (v := v) hu x.2
    refine ⟨k, ?_⟩
    rw [phiMix_apply, hk, Int.cast_mul, zsmul_eq_mul]
    ring
  · rw [Submodule.span_singleton_le_iff_mem]
    obtain ⟨y, hy, hydot⟩ := exists_mem_latOrth_dotZ_eq_gcdMinors2 u v
    refine ⟨⟨y, hy⟩, ?_⟩
    rw [phiMix_apply, hydot]

/-! ## The cardinality of `ZMod Q`-subgroups generated by an integer -/

/-- An integer and its absolute value differ by a sign, in `ZMod Q`. -/
lemma intCast_eq_or_neg_natAbsCast (a : ℤ) (Q : ℕ) :
    ((a : ℤ) : ZMod Q) = ((((a.natAbs : ℕ)) : ℤ) : ZMod Q) ∨
      ((a : ℤ) : ZMod Q) = -((((a.natAbs : ℕ)) : ℤ) : ZMod Q) := by
  rcases Int.natAbs_eq a with h | h
  · exact Or.inl (congrArg (fun z : ℤ => ((z : ℤ) : ZMod Q)) h)
  · refine Or.inr ?_
    rw [← Int.cast_neg]
    exact congrArg (fun z : ℤ => ((z : ℤ) : ZMod Q)) h

/-- The span of an integer in `ZMod Q` has `Q / gcd Q |a|` elements. -/
theorem nat_card_span_int_zmod (Q : ℕ) (hQ : Q ≠ 0) (a : ℤ) :
    Nat.card (Submodule.span ℤ {((a : ℤ) : ZMod Q)}) = Q / Nat.gcd Q a.natAbs := by
  have hiff : ∀ z : ZMod Q, z ∈ Submodule.span ℤ {((a : ℤ) : ZMod Q)}
      ↔ z ∈ AddSubgroup.zmultiples ((a : ℤ) : ZMod Q) := by
    intro z
    rw [Submodule.mem_span_singleton, AddSubgroup.mem_zmultiples_iff]
  have hcard : Nat.card (Submodule.span ℤ {((a : ℤ) : ZMod Q)})
      = Nat.card ↥(AddSubgroup.zmultiples ((a : ℤ) : ZMod Q)) :=
    Nat.card_congr (Equiv.subtypeEquivRight hiff)
  rw [hcard, Nat.card_zmultiples]
  have hsign : addOrderOf ((a : ℤ) : ZMod Q)
      = addOrderOf (((a.natAbs : ℕ)) : ZMod Q) := by
    rcases intCast_eq_or_neg_natAbsCast a Q with h | h
    · rw [h]; congr 1; simp
    · rw [h, addOrderOf_neg]; congr 1; simp
  rw [hsign, ZMod.addOrderOf_coe a.natAbs hQ]

/-! ## The index of `GamMix` in `latOrth u` -/

/-- **The mixed index theorem.**  For primitive `u`, `Q ≥ 1` and arbitrary `v`,
the lattice `latOrth u ⊓ latMod v Q` has the same rank as `latOrth u` and index
`Q / gcd Q |gcdMinors2 u v|`. -/
theorem index_GamMix (u v : ι → ℤ) (hu : IsPrim u) (Q : ℕ) (hQ : 1 ≤ Q) :
    Module.finrank ℤ ↥(latOrth u ⊓ latMod v Q) = Module.finrank ℤ ↥(latOrth u) ∧
    Nat.card (↥(latOrth u) ⧸ (latOrth u ⊓ latMod v Q).comap (latOrth u).subtype)
      = Q / Nat.gcd Q (gcdMinors2 u v).natAbs := by
  have hQ0 : Q ≠ 0 := by omega
  have hQ0i : (Q : ℤ) ≠ 0 := by exact_mod_cast hQ0
  have hker := phiMix_ker u v Q
  have hrange := phiMix_range u v Q hu
  have hcard : Nat.card ((latOrth u) ⧸ (phiMix u v Q).ker) = Nat.card (phiMix u v Q).range :=
    Nat.card_congr (LinearMap.quotKerEquivRange (phiMix u v Q)).toEquiv
  refine ⟨?_, ?_⟩
  · have hrn := Submodule.finrank_quotient_add_finrank (R := ℤ) (M := ↥(latOrth u))
      ((latOrth u ⊓ latMod v Q).comap (latOrth u).subtype)
    have hq : Module.finrank ℤ
        (↥(latOrth u) ⧸ (latOrth u ⊓ latMod v Q).comap (latOrth u).subtype) = 0 := by
      have hQmem : (Q : ℤ) ∈ nonZeroDivisors ℤ := by
        rw [mem_nonZeroDivisors_iff]
        exact ⟨fun y hy => (mul_eq_zero.mp hy).resolve_left hQ0i,
          fun y hy => (mul_eq_zero.mp hy).resolve_right hQ0i⟩
      have hQz : (((Q : ℤ)) : ZMod Q) = 0 := by push_cast; exact ZMod.natCast_self Q
      have htorsQ : Module.IsTorsion ℤ (ZMod Q) := by
        intro y
        refine ⟨⟨(Q : ℤ), hQmem⟩, ?_⟩
        rw [Submonoid.smul_def]
        show ((Q : ℤ)) • y = 0
        rw [zsmul_eq_mul, hQz, zero_mul]
      have htors : Module.IsTorsion ℤ ↥(phiMix u v Q).range := by
        intro x
        obtain ⟨r, hr⟩ := htorsQ (x := (x : ZMod Q))
        exact ⟨r, Subtype.ext (by simpa [Submodule.coe_smul, Submonoid.smul_def] using hr)⟩
      rw [← hker, LinearEquiv.finrank_eq (LinearMap.quotKerEquivRange (phiMix u v Q))]
      exact Module.IsTorsion.finrank_eq_zero (R := ℤ) htors
    have hNL : Module.finrank ℤ ((latOrth u ⊓ latMod v Q).comap (latOrth u).subtype)
        = Module.finrank ℤ ↥(latOrth u ⊓ latMod v Q) :=
      (Submodule.comapSubtypeEquivOfLe inf_le_left).finrank_eq
    omega
  · rw [← hker, hcard, hrange, nat_card_span_int_zmod Q hQ0]

/-! ## Primitivity of the Veronese vector -/

/-- For a primitive `x` and `d ≥ 1`, the Veronese vector `ν_{d,n}(x)` is primitive. -/
theorem isPrim_veronese (d n : ℕ) (hd : 1 ≤ d) {x : Fin (n + 1) → ℤ} (hx : IsPrim x) :
    IsPrim (veronese d n x) := by
  classical
  rw [IsPrim] at hx ⊢
  set D : ℤ := Finset.univ.gcd (veronese d n x) with hD
  have hDnn : 0 ≤ D := Finset.Int.finsetGcd_nonneg
  have hDi : ∀ i : Fin (n + 1), D ∣ x i ^ d := by
    intro i
    have h1 := Finset.gcd_dvd (s := Finset.univ) (f := veronese d n x)
      (Finset.mem_univ (NA.monDi d n i))
    rwa [NA.veronese_monDi] at h1
  have hnat : D.natAbs = 1 := by
    by_contra hne
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
    have hpdvd : (p : ℤ) ∣ D := by
      rw [← Int.natAbs_dvd_natAbs]; simpa using hpd
    have hpx : ∀ i : Fin (n + 1), (p : ℤ) ∣ x i := by
      intro i
      exact Prime.dvd_of_dvd_pow (p := (p : ℤ)) (Nat.prime_iff_prime_int.mp hp)
        (hpdvd.trans (hDi i))
    have hp1 : (p : ℤ) ∣ (1 : ℤ) := by
      rw [← hx]; exact Finset.dvd_gcd fun i _ => hpx i
    have hp1' : p ∣ 1 := by
      have h := Int.natAbs_dvd_natAbs.mpr hp1
      simpa using h
    exact hp.not_dvd_one hp1'
  rcases Int.natAbs_eq_iff.mp hnat with h | h
  · simpa using h
  · omega

/-! ## The determinant of `GamMix` for the Veronese lattice -/

theorem detL_GamMix (d n : ℕ) [DecidableEq (Mon d n)] (hd : 2 ≤ d) (hn : 1 ≤ n)
    (x y : Fin (n + 1) → ℤ)
    (hx : IsPrim x) (hy : IsPrim y) (hxy : LinearIndependent ℤ ![x, y]) (Q : ℕ) (hQ : 1 ≤ Q) :
    detL (GamMix d n x y Q)
      = (Q : ℝ) * eNorm (veronese d n x) / ((Nat.gcd Q (gcdMinors2 x y).natAbs : ℕ) : ℝ) := by
  have hd1 : 1 ≤ d := by omega
  have hu : IsPrim (veronese d n x) := isPrim_veronese d n hd1 hx
  have hidx := index_GamMix (veronese d n x) (veronese d n y) hu Q hQ
  obtain ⟨hfin, hcard⟩ := hidx
  have hdet : detL (latOrth (veronese d n x) ⊓ latMod (veronese d n y) Q)
      = detL (latOrth (veronese d n x)) *
        (Nat.card ((latOrth (veronese d n x)) ⧸
          (latOrth (veronese d n x) ⊓ latMod (veronese d n y) Q).comap
            (latOrth (veronese d n x)).subtype) : ℝ) :=
    GM.detL_index _ _ inf_le_left hfin
  have horth : detL (latOrth (veronese d n x)) = eNorm (veronese d n x) :=
    FM3.detL_latOrth_free _ hu
  have hgcd : Nat.gcd Q (gcdMinors2 (veronese d n x) (veronese d n y)).natAbs
      = Nat.gcd Q (gcdMinors2 x y).natAbs := by
    rw [GM.gcdMinors2_veronese_natAbs d n hd1 hn x y hx hy]
  have hgpos : Nat.gcd Q (gcdMinors2 x y).natAbs ≠ 0 := by
    have h1 : 0 < Nat.gcd Q (gcdMinors2 x y).natAbs := Nat.gcd_pos_of_pos_left _ (by omega)
    omega
  have hcast : ((Q / Nat.gcd Q (gcdMinors2 (veronese d n x) (veronese d n y)).natAbs : ℕ) : ℝ)
      = (Q : ℝ) / ((Nat.gcd Q (gcdMinors2 x y).natAbs : ℕ) : ℝ) := by
    rw [hgcd, Nat.cast_div (Nat.gcd_dvd_left Q (gcdMinors2 x y).natAbs)
      (by exact_mod_cast hgpos)]
  rw [GamMix, hdet, horth, hcard, hcast]
  ring

end Work.HP
