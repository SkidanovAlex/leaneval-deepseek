import Mathlib
import Submission.NK.LocalReciprocityLubinTate.Unramified.Tools
import Submission.NK.LocalReciprocityLubinTate.Eval.ValuationExtension
import Submission.Commons.RingTheory.Henselian.kummer_root_lift

open scoped ValuativeRel

set_option linter.style.haveILetI false

namespace NK.LocalReciprocityLubinTate.Unramified

universe u

/-! ### Plan for the prover

`U¹ = 1 + 𝔪[F]` is `ℓ`-divisible for every prime `ℓ` not equal to the residue characteristic of
`F`.  Two routes are available in the workspace:

* `NK.TameStructureDeep.Units.exists_pow_eq_of_mem_principalUnits` proves exactly this for
  `𝔭.adicCompletionIntegers K` via `Commons.RingTheory.Henselian.kummer_root_lift`; the same
  argument works for `↥𝒪[F]` of a *general* nonarchimedean local field, using
  `NK.LocalReciprocityLubinTate.Eval.henselianLocalRing_integer`
  (`HenselianLocalRing ↥𝒪[F]`) and `Commons.RingTheory.Henselian.kummer_root_lift`
  (`X^ℓ - u` has a root with residue `1` when `ℓ` is a unit and `u` has residue `1`);
* or apply `kummer_root_lift` directly with `p := residueCard F - 1`: its only arithmetic
  requirement is `IsUnit ((residueCard F - 1 : ℕ) : ↥𝒪[F])`, which holds because
  `residueCard F` is a power of the residue characteristic `p = ringChar 𝓀[F]`, so `p ∤ q - 1`.

Details: for `x ∈ higherUnits F 1`, i.e. `x = 1 + m` with `m ∈ 𝔪[F]` (use
`NK.LocalReciprocityLubinTate.mem_principalUnits_iff`), the Kummer polynomial `X^n - x`
(`n = residueCard F - 1`) has residue `X^n - 1`, whose root `1` is simple because `n ≡ -1` in
`𝓀[F]`; Hensel therefore gives `y ∈ 𝒪[F]ˣ` with `y^n = x` and `y ≡ 1 mod 𝔪[F]`, i.e. `y ∈ U¹`.
`x` and `y` are carried into `Fˣ` by `NK.LocalReciprocityLubinTate.Units.unitsIncl`
(`higherUnits F 1` is by definition its image of `principalUnits F 1`). -/

theorem exists_pow_residueCard_sub_one_eq_of_mem_higherUnits_one (F : Type u) [Field F]
    [CharZero F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (x : Fˣ) (hx : x ∈ NK.LocalReciprocityLubinTate.higherUnits F 1) :
    ∃ y ∈ NK.LocalReciprocityLubinTate.higherUnits F 1,
      y ^ (NK.LocalReciprocityLubinTate.residueCard F - 1) = x := by
  classical
  -- the ring of integers is a Henselian local ring
  haveI hhen : HenselianLocalRing ↥𝒪[F] :=
    NK.LocalReciprocityLubinTate.Eval.henselianLocalRing_integer F
  -- the residue field is finite, of characteristic `p` and cardinality `p ^ n`
  letI : Fintype (𝓀[F] : Type u) := Fintype.ofFinite _
  obtain ⟨p, hchar, n, hp, hcard⟩ := FiniteField.card' (𝓀[F] : Type u)
  have hcard' : NK.LocalReciprocityLubinTate.residueCard F = Fintype.card (𝓀[F] : Type u) := by
    rw [NK.LocalReciprocityLubinTate.residueCard, Nat.card_eq_fintype_card]
  have hpow : ((p ^ (n : ℕ) : ℕ) : 𝓀[F]) = 0 := by
    rw [CharP.cast_eq_zero_iff (𝓀[F] : Type u) p]
    exact dvd_pow_self p (PNat.ne_zero n)
  -- hence `residueCard F = 0` in the residue field and `residueCard F - 1 = -1` is a unit
  have hq0 : ((NK.LocalReciprocityLubinTate.residueCard F : ℕ) : 𝓀[F]) = 0 := by
    rw [hcard', hcard]; exact hpow
  have hq1 : 1 ≤ NK.LocalReciprocityLubinTate.residueCard F :=
    le_trans (by norm_num) (NK.LocalReciprocityLubinTate.two_le_residueCard F)
  have hunit : IsUnit ((NK.LocalReciprocityLubinTate.residueCard F - 1 : ℕ) : ↥𝒪[F]) := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, map_natCast, Nat.cast_sub hq1, hq0]
    norm_num
  -- unpack `x` as the image of a principal unit `u`
  rw [NK.LocalReciprocityLubinTate.higherUnits, Subgroup.mem_map] at hx
  obtain ⟨u, hu, hux⟩ := hx
  -- a principal unit reduces to `1`
  have hures : IsLocalRing.residue ↥𝒪[F] (u : ↥𝒪[F]) = 1 := by
    rw [NK.LocalReciprocityLubinTate.mem_principalUnits_iff] at hu
    have h0 : IsLocalRing.residue ↥𝒪[F] ((u : ↥𝒪[F]) - 1) = 0 := by
      rw [IsLocalRing.residue_eq_zero_iff]
      simpa using hu
    rw [map_sub, map_one] at h0
    exact sub_eq_zero.mp h0
  -- Hensel: lift the simple root `1` of `X^(q-1) - u`
  obtain ⟨b, hbpow, hbres⟩ := Commons.RingTheory.Henselian.kummer_root_lift
    (R := ↥𝒪[F]) (NK.LocalReciprocityLubinTate.residueCard F - 1) u.isUnit hunit
    (1 : 𝓀[F]) (by rw [one_pow, hures])
  have hbunit : IsUnit b := by
    rw [← IsLocalRing.residue_ne_zero_iff_isUnit, hbres]
    exact one_ne_zero
  let w : (↥𝒪[F])ˣ := hbunit.unit
  have hwcoe : (w : ↥𝒪[F]) = b := IsUnit.unit_spec hbunit
  have hwpow : w ^ (NK.LocalReciprocityLubinTate.residueCard F - 1) = u := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hwcoe, hbpow]
  -- `b` still reduces to `1`, so `w ∈ U¹`
  have hwmem : w ∈ NK.LocalReciprocityLubinTate.principalUnits F 1 := by
    rw [NK.LocalReciprocityLubinTate.mem_principalUnits_iff]
    have hmm : (w : ↥𝒪[F]) - 1 ∈ IsLocalRing.maximalIdeal ↥𝒪[F] := by
      rw [← IsLocalRing.residue_eq_zero_iff, hwcoe, map_sub, hbres, map_one, sub_self]
    simpa using hmm
  refine ⟨NK.LocalReciprocityLubinTate.Units.unitsIncl F w, ?_, ?_⟩
  · rw [NK.LocalReciprocityLubinTate.higherUnits]
    exact Subgroup.mem_map_of_mem _ hwmem
  · rw [← map_pow, hwpow]
    exact hux


end NK.LocalReciprocityLubinTate.Unramified
