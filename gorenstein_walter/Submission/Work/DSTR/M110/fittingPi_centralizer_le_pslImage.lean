import Mathlib
import Submission.Work.DSTR.Defs
import Submission.Work.DSTR.M110.Conj
import Submission.Work.DSTR.M110.Normalizer.le_pgammaL
import Submission.Work.DSTR.M110.Galois.decomposition
import Submission.Work.DSTR.M110.Aut.centralizer
import Submission.Work.DSTR.M110.Aut.pglIndex
import Submission.Work.DSTR.M110.PiCoreFacts
import Submission.Work.DSTR.M110.SylowGen
import Submission.Work.DSTR.M110.pglInvolutionFixedPoints
import Submission.Work.DSTR.M110.splitCase
import Submission.Work.DSTR.M110.nonsplitCase
import Submission.Work.DSTR.M110.twistCaseProof

/-!
# DS10a in the `ℙ¹` model : `F_{2'}(C_{Q'}(t')) ≤ PSL(2,q)`

This file proves the crux lemma `Work.DSTR.M110.fittingPi_centralizer_le_pslImage`
(Bender 1981, 1.10(ii) in the explicit permutation model of `PΓL(2,q)`):

for `Q'` with `pslImage F ≤ Q' ≤ pgammaL F` (`F = GF(p^k)`, `p` odd, `p^k ≥ 5`) and any
involution `t' ∈ Q'`, the `2'`-part of the Fitting subgroup of the centralizer `C_{Q'}(t')`
lies in `pslImage F`.

The mathematical plan (see the docstrings below and the helper declarations in the
sibling files under `Submission/Work/DSTR/M110/`):

* `N := F_{2'}(C_{Q'}(t'))` is nilpotent of odd order and normal in `C := C_{Q'}(t')`;
* reduced to its Sylow `r`-subgroups (`r` an odd prime) it suffices to show that any
  normal odd `r`-subgroup of `C` lies in `pslImage F`;
* such an `N` either lies in `pglImage F` — and then in `pslImage F` because odd-order
  elements of `PGL(2,q)` are in `PSL(2,q)` — or it contains `x` with non-trivial Galois
  part `γ = σ^i`; conjugating `x` by the cyclic torus `T ⊴ C_{PΓL}(t')` (of order `q ∓ 1`)
  produces `|T| / |C_T(x)|` distinct conjugates, all lying in the coset `x · (N ∩ PGL)`;
  hence `|T| / |C_T(x)| ≤ |T|_r`, i.e. `gcd(|T|, p^i ∓ 1)` is too large — the arithmetic
  lemma `arithOrbitSubOne` / `arithOrbitAddOne`.

## Main definitions

* `negPerm F`   : the canonical split involution `x ↦ -x` of `PΓL(2,F)`;
* `splitTorus F`: the split torus `{x ↦ c·x : c ∈ Fˣ} ≤ PGL(2,F)`.
-/

namespace Work.DSTR.M110

open Work.AUTL2

/-- The canonical **split involution** `x ↦ -x` of `ℙ¹(F)`, an element of `pglImage F`. -/
noncomputable def negPerm (F : Type*) [Field F] [DecidableEq F] : Equiv.Perm (P1 F) :=
  Normalizer.smulPerm F (-1) (neg_ne_zero.mpr one_ne_zero)

@[simp] lemma negPerm_apply_some (F : Type*) [Field F] [DecidableEq F] (x : F) :
    negPerm F (x : P1 F) = ((-x : F) : P1 F) := by
  rw [negPerm, Normalizer.smulPerm_some, neg_one_mul]

@[simp] lemma negPerm_apply_infty (F : Type*) [Field F] [DecidableEq F] :
    negPerm F (OnePoint.infty : P1 F) = OnePoint.infty := by
  rw [negPerm, Normalizer.smulPerm_infty]

lemma negPerm_mem_pglImage (F : Type*) [Field F] [DecidableEq F] :
    negPerm F ∈ pglImage F :=
  Normalizer.smulPerm_mem_pglImage F (-1) _

lemma negPerm_mem_pgammaL (F : Type*) [Field F] [DecidableEq F] :
    negPerm F ∈ pgammaL F := by
  rw [pgammaL]
  exact Subgroup.mem_sup_left (negPerm_mem_pglImage F)

lemma negPerm_involutive (F : Type*) [Field F] [DecidableEq F] :
    negPerm F * negPerm F = 1 := by
  apply Equiv.ext
  rw [OnePoint.forall]
  refine ⟨?_, fun x => ?_⟩
  · rw [Equiv.Perm.mul_apply, negPerm_apply_infty, negPerm_apply_infty, Equiv.Perm.one_apply]
  · rw [Equiv.Perm.mul_apply, negPerm_apply_some, negPerm_apply_some, neg_neg,
      Equiv.Perm.one_apply]

lemma orderOf_negPerm (F : Type*) [Field F] [DecidableEq F] (h2 : (2 : F) ≠ 0) :
    orderOf (negPerm F) = 2 := by
  have hpow : negPerm F ^ 2 = (1 : Equiv.Perm (P1 F)) := by
    rw [pow_two, negPerm_involutive]
  refine orderOf_eq_prime hpow ?_
  intro h
  have h1 := congrFun (congrArg DFunLike.coe h) ((1 : F) : P1 F)
  rw [negPerm_apply_some, Equiv.Perm.one_apply] at h1
  have hneg : (-1 : F) = 1 := OnePoint.coe_eq_coe.mp h1
  refine h2 ?_
  have hzero : (1 : F) + 1 = 0 := by
    rw [← neg_eq_iff_add_eq_zero]
    exact hneg
  rw [← one_add_one_eq_two]
  exact hzero

/-- The **split torus** `{x ↦ c·x : c ∈ Fˣ} ≤ PGL(2,F) ≤ PΓL(2,F)`. -/
noncomputable def splitTorus (F : Type*) [Field F] [DecidableEq F] :
    Subgroup (Equiv.Perm (P1 F)) :=
  Subgroup.closure {g | ∃ c : Fˣ, g = Normalizer.smulPerm F (c : F) (Units.ne_zero c)}

lemma splitTorus_le_pglImage (F : Type*) [Field F] [DecidableEq F] :
    splitTorus F ≤ pglImage F := by
  rw [splitTorus, Subgroup.closure_le]
  rintro g ⟨c, rfl⟩
  exact Normalizer.smulPerm_mem_pglImage F (c : F) (Units.ne_zero c)

lemma negPerm_mem_splitTorus (F : Type*) [Field F] [DecidableEq F] :
    negPerm F ∈ splitTorus F := by
  rw [splitTorus]
  exact Subgroup.subset_closure ⟨-1, rfl⟩

/-- An element of `pglImage F` of **odd** order lies in `pslImage F` (the quotient
`PGL(2,F)/PSL(2,F) ≅ Fˣ/(Fˣ)²` has exponent `2`). -/
theorem oddPglImageMemPslImage (p k : ℕ) [Fact p.Prime] [DecidableEq (GaloisField p k)]
    (x : Equiv.Perm (P1 (GaloisField p k)))
    (hx : x ∈ pglImage (GaloisField p k)) (hodd : Odd (orderOf x)) :
    x ∈ pslImage (GaloisField p k) := by
  -- write `x = pglHom (mk B)` and use that `x ^ 2 ∈ pslImage` (the square of a determinant)
  obtain ⟨g, rfl⟩ := hx
  obtain ⟨B, rfl⟩ := Matrix.ProjGenLinGroup.mk_surjective g
  set x : Equiv.Perm (P1 (GaloisField p k)) :=
    pglHom _ (Matrix.ProjGenLinGroup.mk B) with hxdef
  have hsq : x * x ∈ pslImage (GaloisField p k) := by
    have hxx : x * x = pglHom _ (Matrix.ProjGenLinGroup.mk (B * B)) := by
      rw [hxdef, ← map_mul, ← map_mul]
    rw [hxx, Work.AUTL2.Aut.mem_pslImage_iff_isSquare_det]
    exact ⟨B.det, by rw [map_mul]⟩
  have hm : x ^ orderOf x = 1 := pow_orderOf_eq_one x
  obtain ⟨t, ht⟩ := hodd
  have h2 : 2 * ((orderOf x + 1) / 2) = orderOf x + 1 := by omega
  have hsplit : x = (x * x) ^ ((orderOf x + 1) / 2) := by
    calc x = x ^ (orderOf x + 1) := by rw [pow_succ, hm, one_mul]
      _ = x ^ (2 * ((orderOf x + 1) / 2)) := by rw [h2]
      _ = (x * x) ^ ((orderOf x + 1) / 2) := by rw [pow_mul, pow_two]
  rw [hsplit]
  exact Subgroup.pow_mem _ hsq _

end Work.DSTR.M110

namespace Work.DSTR.M110

open Subgroup

/-- `F_{2'}(K)` has odd order: it is the image of `O_{2'}(F(K))`, which has odd order. -/
theorem odd_card_fittingPiIn {G : Type} [Group G] [Finite G] (K : Subgroup G) :
    Odd (Nat.card ↥(Work.GW2.fittingPiIn ({2}ᶜ : Set ℕ) K)) := by
  have h1 : Odd (Nat.card ↥(Work.GW2.piCore ({2}ᶜ : Set ℕ) ↥(Work.GW2.fitting ↥K))) :=
    Work.GW2.piCore_odd _
  rw [Work.GW2.fittingPiIn, Work.GW2.fittingPi]
  rw [← Nat.card_congr (Subgroup.equivMapOfInjective _ _ (Subgroup.subtype_injective _)).toEquiv,
    ← Nat.card_congr (Subgroup.equivMapOfInjective _ _ (Subgroup.subtype_injective _)).toEquiv]
  exact h1

/-- In a finite nilpotent group the Sylow `r`-subgroups are unique. -/
theorem sylow_eq_of_nilpotent {N : Type} [Group N] [Finite N] [Group.IsNilpotent N]
    (r : ℕ) [Fact r.Prime] (P P' : Sylow r N) : (P : Subgroup N) = P' := by
  have hle : (P' : Subgroup N) ≤ (P : Subgroup N) :=
    IsPGroup.le_sylow_of_normal (p := r) (N := (P' : Subgroup N)) P'.isPGroup' P
  have hcard : Nat.card (P' : Subgroup N) = Nat.card (P : Subgroup N) := by
    rw [Sylow.card_eq_multiplicity (P' : Sylow r N), Sylow.card_eq_multiplicity P]
  exact (Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard.symm)).symm

/-- **DS10a** (Bender 1981, 1.10(ii) in the `ℙ¹` permutation model). -/
theorem fittingPi_centralizer_le_pslImage (p k : ℕ) [Fact p.Prime] (hp : Odd p) (hq : 5 ≤ p ^ k)
    [DecidableEq (GaloisField p k)]
    (Q' : Subgroup (Equiv.Perm (Work.AUTL2.P1 (GaloisField p k))))
    (hpsl : Work.AUTL2.pslImage (GaloisField p k) ≤ Q')
    (hQ : Q' ≤ Work.AUTL2.pgammaL (GaloisField p k))
    (t' : Q') (ht' : orderOf t' = 2) :
    Work.GW2.fittingPiIn {2}ᶜ (Subgroup.centralizer ({t'} : Set Q'))
      ≤ (Work.AUTL2.pslImage (GaloisField p k)).subgroupOf Q' := by
  classical
  haveI : Fintype (GaloisField p k) := Fintype.ofFinite _
  haveI : Fintype (Work.AUTL2.P1 (GaloisField p k)) := Fintype.ofFinite _
  set C : Subgroup ↥Q' := Subgroup.centralizer ({t'} : Set Q') with hCdef
  set N : Subgroup ↥Q' := Work.GW2.fittingPiIn ({2}ᶜ : Set ℕ) C with hNdef
  haveI : Finite ↥Q' := Subtype.finite
  haveI : Finite ↥N := Subtype.finite
  have hNleC : N ≤ C := by rw [hNdef]; exact fittingPiIn_le C
  have hNnil : Group.IsNilpotent ↥N := by rw [hNdef]; exact fittingPiIn_isNilpotent C
  have hNodd : Odd (Nat.card ↥N) := by rw [hNdef]; exact odd_card_fittingPiIn C
  -- Every Sylow subgroup `P` of `N` maps into `pslImage`.  (The proof of this step is the
  -- crux: an odd `r`-subgroup of `C_{Q'}(t')` normal in `C_{Q'}(t')` lies in `pslImage` --
  -- this is where `splitCase` / `nonsplitCase` / `twistCaseProof` are applied, dispatched by
  -- `pglInvolutionFixedPoints`; for `r = 2` the Sylow subgroup is trivial since `|N|` is odd.)
  have hSyl : ∀ (r : ℕ) [Fact r.Prime], Odd r → ∀ P : Sylow r ↥N,
      ((P : Subgroup ↥N).map N.subtype).map Q'.subtype ≤
        Work.AUTL2.pslImage (GaloisField p k) := by
    intro r hrF hrOdd P
    haveI : Fact r.Prime := hrF
    haveI : Group.IsNilpotent ↥N := hNnil
    -- `N = F_{2'}(C)` is normal in `C = C_{Q'}(t')`
    have hNnormC : ∀ c : ↥Q', c ∈ C → ∀ x : ↥Q', x ∈ N → c * x * c⁻¹ ∈ N := by
      have hnorm : C ≤ Subgroup.normalizer ((N : Subgroup ↥Q') : Set ↥Q') := by
        rw [hNdef]
        exact le_normalizer_fittingPiIn (↥Q') ({2}ᶜ : Set ℕ) C
      intro c hc x hx
      exact ((Subgroup.mem_normalizer_iff.mp (hnorm hc)) x).mp hx
    -- the involution `t'`, viewed in `Perm (P¹ F)`
    set t : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k)) :=
      (t' : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k))) with htdef
    have htQ : t ∈ Q' := t'.2
    have ht2 : orderOf t = 2 := by
      have h := Subgroup.orderOf_coe t'
      rw [htdef, h, ht']
    -- the doubly mapped Sylow subgroup of `N`, as a subgroup of `Perm (P¹ F)`
    set Pp : Subgroup (Equiv.Perm (Work.AUTL2.P1 (GaloisField p k))) :=
      ((P : Subgroup ↥N).map N.subtype).map Q'.subtype with hPpdef
    have hPpQ : Pp ≤ Q' := by
      rw [hPpdef]
      rintro x ⟨y, -, rfl⟩
      exact y.2
    have hPpr : IsPGroup r Pp := by
      rw [hPpdef]
      exact (P.isPGroup'.map N.subtype).map Q'.subtype
    have hPpcent : Pp ≤ Subgroup.centralizer
        ({t} : Set (Equiv.Perm (Work.AUTL2.P1 (GaloisField p k)))) := by
      rw [hPpdef]
      rintro x ⟨y, hy, rfl⟩
      obtain ⟨z, -, rfl⟩ := Subgroup.mem_map.mp hy
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      have hzC : N.subtype z ∈ C := hNleC z.2
      have hcomm := (Subgroup.mem_centralizer_iff.mp hzC) t' (Set.mem_singleton t')
      have h1 : (t' : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k))) *
            ((N.subtype z : ↥Q') : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k))) =
          ((N.subtype z : ↥Q') : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k))) *
            (t' : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k))) := by
        simpa only [Subgroup.coe_mul] using
          congrArg (fun w : ↥Q' => (w : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k)))) hcomm
      rw [htdef]
      exact h1
    -- `Pp` is normalized by `C_{Q'}(t')`: `P` is the unique Sylow `r`-subgroup of the
    -- nilpotent group `N`, and conjugation by any `c ∈ C_{Q'}(t')` restricts to an
    -- automorphism of `N`
    have hPpnorm : ∀ c : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k)),
        c ∈ Subgroup.centralizer ({t} : Set (Equiv.Perm (Work.AUTL2.P1 (GaloisField p k)))) →
        c ∈ Q' → ∀ x ∈ Pp, c * x * c⁻¹ ∈ Pp := by
      intro c hc hcQ x hx
      let gc : ↥Q' := ⟨c, hcQ⟩
      have hcC : gc ∈ C := by
        rw [hCdef]
        refine Subgroup.mem_centralizer_iff.mpr ?_
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        rw [hy]
        apply Subtype.ext
        rw [Subgroup.coe_mul, Subgroup.coe_mul]
        rw [← htdef]
        exact (Subgroup.mem_centralizer_iff.mp hc) t (Set.mem_singleton t)
      let φ : ↥N →* ↥N :=
        { toFun := fun w => ⟨gc * (w : ↥Q') * gc⁻¹, hNnormC gc hcC (w : ↥Q') w.2⟩
          map_one' := by
            apply Subtype.ext
            show gc * ((1 : ↥N) : ↥Q') * gc⁻¹ = (1 : ↥Q')
            simp
          map_mul' := by
            intro a b
            apply Subtype.ext
            show gc * ((a * b : ↥N) : ↥Q') * gc⁻¹ =
              (gc * (a : ↥Q') * gc⁻¹) * (gc * (b : ↥Q') * gc⁻¹)
            rw [Subgroup.coe_mul]
            group }
      have hφval : ∀ w : ↥N, ((φ w : ↥N) : ↥Q') = gc * (w : ↥Q') * gc⁻¹ := fun _ => rfl
      have hφinj : Function.Injective φ := by
        intro a b hab
        refine Subtype.ext ?_
        have h := congrArg (fun w : ↥N => (w : ↥Q')) hab
        rw [hφval a, hφval b] at h
        exact mul_left_cancel (mul_right_cancel h)
      have hcardφ : Nat.card ((P : Subgroup ↥N).map φ) =
          r ^ (Nat.card ↥N).factorization r := by
        rw [Subgroup.card_map_of_injective hφinj, Sylow.card_eq_multiplicity P]
      have hmapP : (P : Subgroup ↥N).map φ = P := by
        have h1 := sylow_eq_of_nilpotent r P (Sylow.ofCard ((P : Subgroup ↥N).map φ) hcardφ)
        simpa using h1.symm
      rw [hPpdef] at hx ⊢
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
      obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
      refine Subgroup.mem_map.mpr ⟨N.subtype (φ z), ?_, ?_⟩
      · exact Subgroup.mem_map.mpr
          ⟨φ z, by rw [← hmapP]; exact Subgroup.mem_map.mpr ⟨z, hz, rfl⟩, rfl⟩
      · show Q'.subtype ((φ z : ↥N) : ↥Q') = c * Q'.subtype ((z : ↥N) : ↥Q') * c⁻¹
        rw [hφval z]
        show ((gc * (z : ↥Q') * gc⁻¹ : ↥Q') :
            Equiv.Perm (Work.AUTL2.P1 (GaloisField p k))) =
          c * ((z : ↥Q') : Equiv.Perm (Work.AUTL2.P1 (GaloisField p k))) * c⁻¹
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    -- dispatch: `t' ∈ PGL` with two fixed points / fixed-point-free, or twisted
    by_cases htpgl : t ∈ Work.AUTL2.pglImage (GaloisField p k)
    · rcases pglInvolutionFixedPoints p k hp t htpgl ht2 with
        ⟨a, b, hab, ha, hb⟩ | hfpf
      · exact splitCase p k r hp hq hrF.out hrOdd Q' hpsl hQ t htQ ht2 htpgl a b hab ha hb
          Pp hPpQ hPpcent hPpnorm hPpr
      · exact nonsplitCase p k r hp hq hrF.out hrOdd Q' hpsl hQ t htQ ht2 htpgl hfpf
          Pp hPpQ hPpcent hPpnorm hPpr
    · exact twistCaseProof p k r hp hq hrF.out hrOdd Q' hpsl hQ t htQ ht2 htpgl
        Pp hPpQ hPpcent hPpnorm hPpr
  have key : ((Work.AUTL2.pslImage (GaloisField p k)).subgroupOf Q').comap N.subtype = ⊤ := by
    refine eq_top_of_sylow_le (L := ((Work.AUTL2.pslImage (GaloisField p k)).subgroupOf
      Q').comap N.subtype) fun r hrF P => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    have hPq : ((P : Subgroup ↥N).map N.subtype).map Q'.subtype ≤
        Work.AUTL2.pslImage (GaloisField p k) := by
      rcases hrF.out.eq_two_or_odd with h2 | hodd
      · -- `r = 2`: `P` is trivial because `|N|` is odd
        subst h2
        have hcard : Nat.card (P : Subgroup ↥N) = 2 ^ (Nat.card ↥N).factorization 2 :=
          Sylow.card_eq_multiplicity P
        have hfac : (Nat.card ↥N).factorization 2 = 0 := by
          refine Nat.factorization_eq_zero_of_not_dvd ?_
          rw [← even_iff_two_dvd]
          exact Nat.not_even_iff_odd.mpr hNodd
        have hbot : (P : Subgroup ↥N) = ⊥ := by
          rw [Subgroup.eq_bot_iff_card, hcard, hfac, pow_zero]
        rw [hbot]
        simp
      · exact hSyl r (Nat.odd_iff.mpr hodd) P
    rwa [Subgroup.map_le_iff_le_comap] at hPq
  intro x hx
  have : (⟨x, hx⟩ : ↥N) ∈ ((Work.AUTL2.pslImage (GaloisField p k)).subgroupOf Q').comap
      N.subtype := by
    rw [key]; trivial
  exact this

end Work.DSTR.M110
