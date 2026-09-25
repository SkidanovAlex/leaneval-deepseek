import Mathlib
import Submission.NK.GlobalCFTdeep.Existence
import Submission.NK.GlobalCFT.NormGroup.Basic
import Submission.NK.NUV2.ArtinBridge.exists_le_index_eq_prime
import Submission.NK.NUV2.ArtinBridge.isOpen_comap_normClassHom
import Submission.NK.NUV2.ArtinBridge.kummerKeyCaseHerbrand
import Submission.NK.NUV2.ArtinBridge.normLimitation
import Submission.NK.CFTLib.fundamentalClassElement
import Submission.NK.GlobalCFTdeep.FundamentalClassReduction
import Submission.NK.GlobalCFTdeep.H1All

/-!
# Takagi's existence theorem (the existence half of global class field theory)

Target: `NK.GlobalCFTdeep.TakagiExistence.{0,0} K` for every number field `K`: every open
subgroup of finite index of the idèle class group `C[K]` contains the norm group `N_{L/K}C_L` of a
finite abelian extension `L/K`.

The proof follows Milne, *Class Field Theory*, Theorem 9.5 (in its **weak** form — we only produce a
norm group *contained* in the given subgroup, which is what `TakagiExistence` asks for; the upgrade
to `N_{L/K}C_L = N` is Milne's Lemma 9.1 and uses the reciprocity law).

* `TakagiKeyCase` (Milne, CFT, Lemma 9.3): the Kummer key case over a field containing `ζ_p`.
* `IndexPrimeTheorem`: a subgroup of index divisible by `p` is contained in one of index `p`.
* `NormPreimageOpen`: the preimage of an open subgroup under the norm map is open (the idèlic norm
  is continuous).
* `Descent` (Milne, CFT, Lemma 9.4 together with the Norm Limitation Theorem): if `N_{L/K₁}C_L` is
  contained in the preimage of `N ≤ C[K]`, then some *abelian* `M/K` has `N_{M/K}C_M ≤ N`.
* `MainZ n` / `Main n`: the induction on the index `n = [C_K : N]`, proved in `main_aux`; `MainZ`
  is the same statement with the extra hypothesis that `K` contains a primitive `q`-th root of
  unity for every prime `q ∣ n` (the form in which the key case applies).

## The structure of the induction (`main_aux`)

`MainZ n` and `Main n` are proved simultaneously by strong induction on `n`.

*`MainZ n`* (Milne 9.5, the case `K ∋ ζ_q` for `q ∣ n`): if `[C_K : N] = n > 1`, pick a prime
`p ∣ n` and, by `IndexPrimeTheorem`, a subgroup `V ⊇ N` of index `p`.  The key case over `K`
(`K ∋ ζ_p`) produces a finite abelian `K'/K` with `N_{K'/K}C_{K'} ≤ V`.  Put
`N' = Nm_{K'/K}^{-1}(N) ≤ C_{K'}`.  The index arithmetic
`N'.index * (N ⊔ Nm_{K'/K}C_{K'}).index = n` shows `N'.index ∣ n`, and since
`N ⊔ Nm_{K'/K}C_{K'} ≤ V` we have `(N ⊔ Nm C_{K'}).index ≥ p`, so either `N' = ⊤` (and then
`N_{K'/K}C_{K'} ≤ N`, done with `L = K'`) or `N'.index < n`.  In the latter case the induction
hypothesis over `K'` (which contains `ζ_q` for every `q ∣ N'.index`, since `N'.index ∣ n` and
`K ⊆ K'`) produces `L/K'` abelian with `N_{L/K'}C_L ≤ N'`, and `Descent` finishes.

*`Main n`* (arbitrary `K`): by `Descent` it suffices to find a finite extension `K₁/K` whose
preimage of `N` is a norm group over `K₁`.  Take `K₁ = K(ζ_n)` (the cyclotomic field), so that
`K₁` contains `ζ_q` for every prime `q ∣ n`; the preimage `N₁ = Nm_{K₁/K}^{-1}(N)` satisfies
`N₁.index ∣ n`, `N₁.index ≤ n`, so `MainZ N₁.index` (the induction hypothesis, or the just-proved
`MainZ n` when `N₁.index = n`) applies over `K₁`, and `Descent` finishes.

## Status

`main` (and its auxiliary form `main_aux : ∀ n, MainZ n ∧ Main n`) is **proved** — the induction on
the index is complete, see `main_aux`.  The remaining distance to the challenge statement is the
conjunction of the two inputs `TakagiKeyCase` and `Descent`, both of which are consequences of the
global fundamental class / Artin reciprocity (the workspace's crux):

* `TakagiKeyCase` is obtained from the abelian index formula `[C_K : N_{L/K}C_L] = [L:K]`, i.e. from
  `NK.GlobalCFT.HerbrandQuotient K L` for abelian `L/K`; the reduction (adapting the sorry-free
  proof of `NK.NUV2.ArtinBridge.kummerKeyCase`, whose single use of the `sorry`-tainted
  `NK.CFTLib.Existence.index_eq_finrank_of_isAbelian` is replaced by
  `index_eq_finrank_of_abelian_of_herbrand`) is delegated as
  `NK.NUV2.ArtinBridge.kummerKeyCaseHerbrand`.
* `Descent` is Milne's Lemma 9.4 together with the Norm Limitation Theorem (Milne, CFT, 4.8); the
  reduction from the fundamental class is delegated as `NK.NUV2.ArtinBridge.normLimitation`.

See `NOTES_takagiExistence.md` in this directory for the full bookkeeping, including the recorded
analysis showing that both inputs are genuinely equivalent in strength to the global fundamental
class (the tower multiplicativity of the Herbrand quotient is false for general modules and fails
for `A = C_L`, `G = S₃`, `H = A₃` — the Hasse norm defect `Ĥ^{-1}(H,C_L) ≅ H₂(H,ℤ)` is the
obstruction).

## The exact remaining gaps

The target is reduced to four precisely-stated inputs, collected here as `Prop`-valued definitions:

* `IndexPrimeTheorem` — **proved** in `NK.NUV2.ArtinBridge.exists_le_index_eq_prime`
  (finite abelian quotient + the structure theorem), exposed here as `indexPrimeTheorem`;
* `NormPreimageOpen` — **proved** in `NK.NUV2.ArtinBridge.isOpen_comap_normClassHom`
  (which proves continuity of the idèlic norm `N_{L/K} : 𝕀 L → 𝕀 K` and of
  `normClassHom : C_L →* C_K`), exposed here as `normPreimageOpen`;
* `TakagiKeyCase` — Milne, *CFT*, Lemma 9.3 (Kummer theory over `K ∋ ζ_p`); proved in
  `NK.NUV2.ArtinBridge.kummerKeyCase` modulo the **abelian index formula**
  `[C_K : N_{L/K}C_L] = [L:K]` for finite abelian `L/K` (Milne uses the Reciprocity Law here:
  "from the Reciprocity Law, `(I_K : K^× Nm(I_L)) = [L:K]`"), which in this workspace is the
  arithmetic input `NK.GlobalCFTdeep.FundamentalClassElement` / Artin reciprocity;  the
  sorry-free reduction from `HerbrandQuotient` is delegated as
  `NK.NUV2.ArtinBridge.kummerKeyCaseHerbrand`;
* `Descent` — Milne, *CFT*, Lemma 9.4 with the **Norm Limitation Theorem** (the norm group of
  `L/K` equals that of its maximal abelian subextension); proved from the fundamental class by
  Milne, *CFT*, Theorem 4.8; the reduction is delegated as
  `NK.NUV2.ArtinBridge.normLimitation`.

`takagiExistence_of` assembles the target from `TakagiKeyCase` and `Descent`; the induction
`main` (strong induction on the index) is now **proved** in `main_aux`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField IsMulCommutative
open NK.GlobalCFT

noncomputable section

namespace NK.NUV2.ArtinBridge

/-- **Takagi's key case** (Milne, CFT, Lemma 9.3): over a number field `K` containing a primitive
`p`-th root of unity, every open subgroup of index `p` of the idèle class group contains the norm
group of a finite abelian extension. -/
def TakagiKeyCase : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime] (ζ : K),
    IsPrimitiveRoot ζ p → ∀ (V : Subgroup C[K]), V.FiniteIndex →
      IsOpen (V : Set C[K]) → V.index = p →
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L)
      (_ : FiniteDimensional K L) (_ : IsGalois K L) (_ : IsMulCommutative (L ≃ₐ[K] L)),
      Idele.normClassSubgroup K L ≤ V

/-- **Index-`p` subgroups**: a finite-index subgroup of a commutative group whose index is
divisible by `p` is contained in a subgroup of index `p`. -/
def IndexPrimeTheorem : Prop :=
  ∀ {G : Type} [CommGroup G] (N : Subgroup G) (p : ℕ), Fact p.Prime → N.FiniteIndex →
    p ∣ N.index → ∃ V : Subgroup G, N ≤ V ∧ V.index = p

/-- **Openness of norm preimages**: the preimage of an open subgroup of `C[K]` under the norm map
`N_{L/K} : C[L] →* C[K]` is open (the idèlic norm is continuous, and the quotient map is open). -/
def NormPreimageOpen : Prop :=
  ∀ (K L : Type) [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
    [FiniteDimensional K L] (N : Subgroup C[K]), IsOpen (N : Set C[K]) →
    IsOpen ((N.comap (IdeleClassGroup.normClassHom K L) : Subgroup C[L]) : Set C[L])

/-- **The descent step** (Milne, CFT, Lemma 9.4 with the Norm Limitation Theorem): if the norm
group `N_{L/K₁}C_L` is contained in the preimage under `N_{K₁/K}` of a subgroup `N ≤ C[K]`, then
`N` contains the norm group of a finite abelian extension `M/K`.

This is Milne's Lemma 9.4: the norm group of `L/K₁` pushes down to a subgroup of `C_K` contained
in `N`, and the Norm Limitation Theorem (Milne, CFT, Theorem 4.8) replaces the — possibly
non-abelian — extension `L/K` by its maximal abelian subextension.  We keep the hypotheses
`K₁/K` abelian and `L/K₁` abelian, under which the theorem is applied. -/
def Descent : Prop :=
  ∀ (K K₁ L : Type) [Field K] [NumberField K] [Field K₁] [NumberField K₁] [Field L]
    [NumberField L] [Algebra K K₁] [FiniteDimensional K K₁] [Algebra K₁ L] [FiniteDimensional K₁ L]
    [IsGalois K K₁] [IsMulCommutative (K₁ ≃ₐ[K] K₁)]
    [IsGalois K₁ L] [IsMulCommutative (L ≃ₐ[K₁] L)]
    (N : Subgroup C[K]),
    Idele.normClassSubgroup K₁ L ≤ N.comap (IdeleClassGroup.normClassHom K K₁) →
    ∃ (M : Type) (_ : Field M) (_ : NumberField M) (_ : Algebra K M) (_ : FiniteDimensional K M)
      (_ : IsGalois K M) (_ : IsMulCommutative (M ≃ₐ[K] M)), Idele.normClassSubgroup K M ≤ N

/-- **The induction statement**: every open finite-index subgroup of `C[K]` of index `n` contains
the norm group of a finite abelian extension of `K`. -/
def Main (n : ℕ) : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (N : Subgroup C[K]), N.FiniteIndex →
    IsOpen (N : Set C[K]) → N.index = n →
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L)
      (_ : FiniteDimensional K L) (_ : IsGalois K L) (_ : IsMulCommutative (L ≃ₐ[K] L)),
      Idele.normClassSubgroup K L ≤ N

/-- **The induction statement over fields containing the relevant roots of unity**: as `Main n`,
but for number fields `K` which contain a primitive `q`-th root of unity for every prime `q ∣ n`
(the hypothesis under which Milne's key case applies at the first step of the induction). -/
def MainZ (n : ℕ) : Prop :=
  ∀ (K : Type) [Field K] [NumberField K],
    (∀ q : ℕ, q.Prime → q ∣ n → ∃ ζ : K, IsPrimitiveRoot ζ q) →
    ∀ (N : Subgroup C[K]), N.FiniteIndex → IsOpen (N : Set C[K]) → N.index = n →
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra K L)
      (_ : FiniteDimensional K L) (_ : IsGalois K L) (_ : IsMulCommutative (L ≃ₐ[K] L)),
      Idele.normClassSubgroup K L ≤ N

/-- The group of `K`-algebra automorphisms of `K` itself is commutative (it is the trivial
group). -/
theorem isMulCommutative_algEquiv_self (K : Type) [Field K] : IsMulCommutative (K ≃ₐ[K] K) :=
  ⟨⟨fun a b => Subsingleton.elim _ _⟩⟩

/-- The `K = L` instance of the induction conclusion: `N_{K/K}C_K = ⊤ ≤ N` for `N = ⊤`. -/
private theorem main_one : Main 1 := by
  intro K _ _ N hfi hop hidx
  refine ⟨K, inferInstance, inferInstance, inferInstance, inferInstance, IsGalois.self K,
    isMulCommutative_algEquiv_self K, ?_⟩
  rw [Subgroup.index_eq_one.mp hidx]
  exact le_top

private theorem mainZ_one : MainZ 1 := by
  intro K _ _ hζ N hfi hop hidx
  exact main_one K N hfi hop hidx

/-- **The simultaneous strong induction** underlying Milne's Theorem 9.5: for every `n`,
`MainZ n` (the key-case-friendly form) and `Main n` hold. -/
theorem main_aux (hKey : TakagiKeyCase) (hIdx : IndexPrimeTheorem) (hPre : NormPreimageOpen)
    (hDesc : Descent) : ∀ n : ℕ, MainZ n ∧ Main n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    have ihZ : ∀ m < n, MainZ m := fun m hm => (ih m hm).1
    have hZ : MainZ n := by
      intro K _ _ hζ N hfi hop hidx
      by_cases hn1 : n = 1
      · have htop : N = ⊤ := Subgroup.index_eq_one.mp (by rw [hidx, hn1])
        refine ⟨K, inferInstance, inferInstance, inferInstance, inferInstance, IsGalois.self K,
          isMulCommutative_algEquiv_self K, ?_⟩
        rw [htop]
        exact le_top
      · obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd hn1
        have hpN : p ∣ N.index := by rw [hidx]; exact hpdvd
        obtain ⟨V, hNV, hVidx⟩ := hIdx N p ⟨hp⟩ hfi hpN
        have hVopen : IsOpen (V : Set C[K]) := Subgroup.isOpen_mono hNV hop
        have hVfi : V.FiniteIndex :=
          Subgroup.finiteIndex_iff.mpr (by rw [hVidx]; exact hp.ne_zero)
        obtain ⟨ζ, hζp⟩ := hζ p hp hpdvd
        haveI : Fact p.Prime := ⟨hp⟩
        obtain ⟨K', hField', hNF', hAlg', hFD', hGal', hComm', hle'⟩ :=
          hKey K p ζ hζp V hVfi hVopen hVidx
        letI : Field K' := hField'
        letI : NumberField K' := hNF'
        letI : Algebra K K' := hAlg'
        letI : FiniteDimensional K K' := hFD'
        letI : IsGalois K K' := hGal'
        letI : IsMulCommutative (K' ≃ₐ[K] K') := hComm'
        -- the preimage of `N` in `C_{K'}`
        let f := IdeleClassGroup.normClassHom K K'
        let N' : Subgroup C[K'] := N.comap f
        have hN'open : IsOpen (N' : Set C[K']) := hPre K K' N hop
        -- index arithmetic: `N'.index * [C_K : N ⊔ Nm C_{K'}] = n`
        have hn0 : n ≠ 0 := by
          rintro rfl
          exact (Subgroup.finiteIndex_iff.mp hfi) (by rw [hidx])
        have hcomap : N'.index = N.relIndex f.range := Subgroup.index_comap N f
        have hsup : N.relIndex (N ⊔ f.range) = N.relIndex f.range :=
          Subgroup.relIndex_sup_left f.range N
        have hNfi : N.FiniteIndex := hfi
        have hmul : N'.index * (N ⊔ f.range).index = n := by
          rw [hcomap, ← hsup, Subgroup.relIndex_mul_index le_sup_left, hidx]
        have hmdvd : N'.index ∣ n := ⟨(N ⊔ f.range).index, hmul.symm⟩
        have hkpos : (N ⊔ f.range).index ≠ 0 :=
          fun h0 => hn0 (by rw [← hmul, h0, mul_zero])
        have hN'fi : N'.FiniteIndex :=
          Subgroup.finiteIndex_iff.mpr (fun h0 => hn0 (by rw [← hmul, h0, zero_mul]))
        haveI : (N ⊔ f.range).FiniteIndex := Subgroup.finiteIndex_iff.mpr hkpos
        have hrange_le : f.range ≤ V := by
          have h := hle'
          rwa [NK.GlobalCFT.Idele.normClassSubgroup_eq_range] at h
        have hkp : p ≤ (N ⊔ f.range).index := by
          have hleV : N ⊔ f.range ≤ V := sup_le hNV hrange_le
          have h := Subgroup.index_antitone hleV
          rw [hVidx] at h
          exact h
        by_cases hm1 : N'.index = 1
        · -- the norm group of `K'` already lies in `N`
          have htop : N' = ⊤ := Subgroup.index_eq_one.mp hm1
          have hrle : f.range ≤ N := by
            rw [MonoidHom.range_eq_map]
            exact (Subgroup.map_le_iff_le_comap).mpr
              (le_of_eq (show (⊤ : Subgroup C[K']) = N.comap f from htop.symm))
          refine ⟨K', hField', hNF', hAlg', hFD', hGal', hComm', ?_⟩
          rw [NK.GlobalCFT.Idele.normClassSubgroup_eq_range]
          exact hrle
        · -- the index drops strictly: apply the induction hypothesis over `K'`
          have hN'ne : N'.index ≠ 0 := Subgroup.finiteIndex_iff.mp hN'fi
          have hm2 : 2 ≤ N'.index := by omega
          have hmpos : 0 < N'.index := by omega
          have hmltn : N'.index < n := by
            have hk2 : 1 < (N ⊔ f.range).index := lt_of_lt_of_le (by norm_num) (le_trans hp.two_le hkp)
            calc N'.index = N'.index * 1 := (mul_one _).symm
              _ < N'.index * (N ⊔ f.range).index := Nat.mul_lt_mul_of_pos_left hk2 hmpos
              _ = n := hmul
          have hζ' : ∀ q : ℕ, q.Prime → q ∣ N'.index → ∃ ζ' : K', IsPrimitiveRoot ζ' q := by
            intro q hq hqm
            obtain ⟨ζ₀, hζ₀⟩ := hζ q hq (dvd_trans hqm hmdvd)
            exact ⟨algebraMap K K' ζ₀,
              hζ₀.map_of_injective (algebraMap K K').injective⟩
          obtain ⟨L, hFieldL, hNFL, hAlgL, hFDL, hGalL, hCommL, hleL⟩ :=
            ihZ N'.index hmltn K' hζ' N' hN'fi hN'open rfl
          letI : Field L := hFieldL
          letI : NumberField L := hNFL
          letI : Algebra K' L := hAlgL
          letI : FiniteDimensional K' L := hFDL
          letI : IsGalois K' L := hGalL
          letI : IsMulCommutative (L ≃ₐ[K'] L) := hCommL
          obtain ⟨M, hFieldM, hNFM, hAlgM, hFDM, hGalM, hCommM, hleM⟩ :=
            hDesc K K' L N hleL
          exact ⟨M, hFieldM, hNFM, hAlgM, hFDM, hGalM, hCommM, hleM⟩
    refine ⟨hZ, ?_⟩
    -- ### the general case: pass to `K(ζ_n)` and use `MainZ`
    intro K _ _ N hfi hop hidx
    haveI : N.FiniteIndex := hfi
    by_cases hn1 : n = 1
    · have htop : N = ⊤ := Subgroup.index_eq_one.mp (by rw [hidx, hn1])
      refine ⟨K, inferInstance, inferInstance, inferInstance, inferInstance, IsGalois.self K,
        isMulCommutative_algEquiv_self K, ?_⟩
      rw [htop]
      exact le_top
    · have hn0 : n ≠ 0 := by
        rintro rfl
        exact (Subgroup.finiteIndex_iff.mp hfi) (by rw [hidx])
      -- the cyclotomic field `K(ζ_n)`
      haveI : NeZero n := ⟨hn0⟩
      let K₁ := CyclotomicField n K
      haveI : IsCyclotomicExtension {n} K K₁ := inferInstance
      haveI : IsGalois K K₁ := IsCyclotomicExtension.isGalois {n} K K₁
      haveI : IsMulCommutative (K₁ ≃ₐ[K] K₁) := IsCyclotomicExtension.isMulCommutative {n} K K₁
      let f := IdeleClassGroup.normClassHom K K₁
      let N₁ : Subgroup C[K₁] := N.comap f
      have hN₁open : IsOpen (N₁ : Set C[K₁]) := hPre K K₁ N hop
      have hcomap : N₁.index = N.relIndex f.range := Subgroup.index_comap N f
      have hsup : N.relIndex (N ⊔ f.range) = N.relIndex f.range :=
        Subgroup.relIndex_sup_left f.range N
      have hmul : N₁.index * (N ⊔ f.range).index = n := by
        rw [hcomap, ← hsup, Subgroup.relIndex_mul_index le_sup_left, hidx]
      have hmdvd : N₁.index ∣ n := ⟨(N ⊔ f.range).index, hmul.symm⟩
      have hmle : N₁.index ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) hmdvd
      have hN₁fi : N₁.FiniteIndex :=
        Subgroup.finiteIndex_iff.mpr (fun h0 => hn0 (by rw [← hmul, h0, zero_mul]))
      haveI : (N ⊔ f.range).FiniteIndex :=
        Subgroup.finiteIndex_iff.mpr (fun h0 => hn0 (by rw [← hmul, h0, mul_zero]))
      -- `K₁` contains a primitive `q`-th root of unity for every prime `q ∣ n`
      have hζ₁ : ∀ q : ℕ, q.Prime → q ∣ n → ∃ ζ : K₁, IsPrimitiveRoot ζ q := by
        intro q hq hqn
        obtain ⟨ζn, hζn⟩ :=
          IsCyclotomicExtension.exists_isPrimitiveRoot (S := {n}) K K₁ (Set.mem_singleton n) hn0
        refine ⟨ζn ^ (n / q), hζn.pow (Nat.pos_of_ne_zero hn0) ?_⟩
        rw [Nat.div_mul_cancel hqn]
      rcases lt_or_eq_of_le hmle with hlt | heq
      · obtain ⟨L, hFieldL, hNFL, hAlgL, hFDL, hGalL, hCommL, hleL⟩ :=
          ihZ N₁.index hlt K₁ (fun q hq hqm => hζ₁ q hq (dvd_trans hqm hmdvd)) N₁ hN₁fi
            hN₁open rfl
        letI : Field L := hFieldL
        letI : NumberField L := hNFL
        letI : Algebra K₁ L := hAlgL
        letI : FiniteDimensional K₁ L := hFDL
        letI : IsGalois K₁ L := hGalL
        letI : IsMulCommutative (L ≃ₐ[K₁] L) := hCommL
        obtain ⟨M, hFieldM, hNFM, hAlgM, hFDM, hGalM, hCommM, hleM⟩ :=
          hDesc K K₁ L N hleL
        exact ⟨M, hFieldM, hNFM, hAlgM, hFDM, hGalM, hCommM, hleM⟩
      · obtain ⟨L, hFieldL, hNFL, hAlgL, hFDL, hGalL, hCommL, hleL⟩ :=
          hZ K₁ (fun q hq hqm => hζ₁ q hq (heq ▸ hqm)) N₁ hN₁fi hN₁open heq
        letI : Field L := hFieldL
        letI : NumberField L := hNFL
        letI : Algebra K₁ L := hAlgL
        letI : FiniteDimensional K₁ L := hFDL
        letI : IsGalois K₁ L := hGalL
        letI : IsMulCommutative (L ≃ₐ[K₁] L) := hCommL
        obtain ⟨M, hFieldM, hNFM, hAlgM, hFDM, hGalM, hCommM, hleM⟩ :=
          hDesc K K₁ L N hleL
        exact ⟨M, hFieldM, hNFM, hAlgM, hFDM, hGalM, hCommM, hleM⟩

/-- **The induction of Milne's Theorem 9.5** (Milne, *CFT*, IX.9.3–9.5): for every `n`, every
open finite-index subgroup of index `n` of `C[K]` contains the norm group of a finite abelian
extension of `K`. -/
theorem main (hKey : TakagiKeyCase) (hIdx : IndexPrimeTheorem) (hPre : NormPreimageOpen)
    (hDesc : Descent) : ∀ n : ℕ, Main n :=
  fun n => (main_aux hKey hIdx hPre hDesc n).2

/-- `IndexPrimeTheorem` is a theorem (see
`NK.NUV2.ArtinBridge.exists_le_index_eq_prime`). -/
theorem indexPrimeTheorem : IndexPrimeTheorem :=
  fun N p hp hN hdiv => @exists_le_index_eq_prime _ _ N p hp hN hdiv

/-- `NormPreimageOpen` is a theorem (see
`NK.NUV2.ArtinBridge.isOpen_comap_normClassHom`). -/
theorem normPreimageOpen : NormPreimageOpen :=
  fun K L _ _ _ _ _ _ N hN => isOpen_comap_normClassHom K L N hN

/-- **Milne's key case from the abelian Herbrand-quotient computation.**

This is the reduction of `TakagiKeyCase` to the abelian index formula in the form
`NK.GlobalCFT.HerbrandQuotient K L` (Milne, *CFT*, Theorem 4.3 for abelian `L/K`): given the
Herbrand-quotient computation, `index_eq_finrank_of_abelian_of_herbrand` gives the index formula,
which is the only arithmetic input of `NK.NUV2.ArtinBridge.kummerKeyCaseHerbrand`. -/
theorem takagiKeyCase_of_herbrand
    (hh : ∀ {K' L' : Type} [Field K'] [NumberField K'] [Field L'] [NumberField L'] [Algebra K' L']
      [FiniteDimensional K' L'] [IsGalois K' L'] [IsMulCommutative (L' ≃ₐ[K'] L')],
      NK.GlobalCFT.HerbrandQuotient K' L') : TakagiKeyCase :=
  fun K _ _ p _ ζ hζ V hV hVopen hVidx =>
    kummerKeyCaseHerbrand hh K p ζ hζ V hV hVopen hVidx

/-- **The abelian Herbrand-quotient computation from the global fundamental class.**

For a finite **abelian** extension `L/K` of number fields, the global fundamental class
(`NK.GlobalCFTdeep.FundamentalClassElement`, via the cohomological field axiom) gives the index
formula `[C_K : N_{L/K}C_L] = [L:K]`, and with `H¹(G, C_L) = 0` (unconditional, `H1All`) this is
the Herbrand-quotient computation `|Ĥ⁰(G,C_L)| = [L:K]·|Ĥ¹(G,C_L)|`.

This is Milne, *CFT*, Theorem 4.3 in the **abelian** case (the on-disk
`herbrandQuotient_of_cohomologicalFieldAxiom` covers only the cyclic case). -/
theorem abelianHerbrand_of_fundamentalClass (hFC : NK.GlobalCFTdeep.FundamentalClassElement) :
    ∀ {K L : Type} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
      [FiniteDimensional K L] [IsGalois K L] [IsMulCommutative (L ≃ₐ[K] L)],
      NK.GlobalCFT.HerbrandQuotient K L := by
  intro K L _ _ _ _ _ _ _ _
  -- `Ĥ¹(G, C_L) ≅ H¹(G, C_L) = 0`, hence `|Ĥ¹(G, C_L)| = 1`.
  have hcard1 : Nat.card (tateCohomology (NK.GlobalCFT.IdeleClassGroup.rep K L) 1) = 1 := by
    have hsub : Subsingleton (tateCohomology (NK.GlobalCFT.IdeleClassGroup.rep K L) 1) :=
      Commons.RepresentationTheory.TateCohomology.subsingleton_tateCohomology_of_subsingleton_groupCohomology
        _ 1 (NK.GlobalCFTdeep.subsingleton_groupCohomology_one_ideleClassGroup (F := K) (E := L))
    exact Nat.card_eq_one_iff_unique.mpr ⟨hsub, ⟨0⟩⟩
  -- the field axiom (hence the index formula) from the fundamental class
  have hfa : NK.GlobalCFT.FieldAxiom K L :=
    NK.GlobalCFT.fieldAxiom_of_cohomologicalFieldAxiom
      (NK.GlobalCFTdeep.cohomologicalFieldAxiom_of_fundamentalClassElement hFC)
      (NK.GlobalCFT.globalCFT_H0Computation (K := K) (L := L))
  have h0 : Nat.card (tateCohomology (NK.GlobalCFT.IdeleClassGroup.rep K L) 0)
      = Module.finrank K L := by
    rw [← NK.GlobalCFT.H0Computation.index_eq_natCard
      (NK.GlobalCFT.globalCFT_H0Computation (K := K) (L := L))]
    exact hfa.index_eq
  refine ⟨?_, ?_⟩
  · rw [hcard1]; norm_num
  · rw [h0, hcard1, mul_one]

/-- **Milne's key case from the global fundamental class.** -/
theorem takagiKeyCase_of_fundamentalClass (hFC : NK.GlobalCFTdeep.FundamentalClassElement) :
    TakagiKeyCase :=
  takagiKeyCase_of_herbrand (abelianHerbrand_of_fundamentalClass hFC)

/-- **The main induction, with the index-`p` and openness inputs discharged.** -/
theorem main' (hKey : TakagiKeyCase) (hDesc : Descent) : ∀ n : ℕ, Main n :=
  main hKey indexPrimeTheorem normPreimageOpen hDesc

/-- **Takagi's existence theorem** (Milne, *CFT*, Theorem 9.5, weak form): every open subgroup of
finite index of the idèle class group contains the norm group of a finite abelian extension. -/
theorem takagiExistence_of (hKey : TakagiKeyCase) (hDesc : Descent)
    (K : Type) [Field K] [NumberField K] :
    NK.GlobalCFTdeep.TakagiExistence.{0, 0} K :=
  ⟨fun N hfi hop => (main' hKey hDesc N.index K N hfi hop rfl)⟩

/-- **The descent step (Milne 9.4 + the Norm Limitation Theorem 4.8) from the global fundamental
class.**  See `NK.NUV2.ArtinBridge.normLimitation`, which proves Milne's Theorem 4.8 (the norm
group of a finite extension is that of its maximal abelian subextension) from the fundamental
class and derives this statement. -/
theorem descent_of_fundamentalClass (hFC : NK.GlobalCFTdeep.FundamentalClassElement) : Descent :=
  normLimitation hFC

/-- **Takagi's existence theorem from the global fundamental class.**

Both inputs are now consequences of `NK.GlobalCFTdeep.FundamentalClassElement`:
`TakagiKeyCase` through the abelian Herbrand-quotient computation
(`abelianHerbrand_of_fundamentalClass`, i.e. Milne's Theorem 4.3 for abelian extensions, the index
formula), and `Descent` through the Norm Limitation Theorem (`descent_of_fundamentalClass`). -/
theorem takagiExistence_of_fundamentalClass (hFC : NK.GlobalCFTdeep.FundamentalClassElement)
    (K : Type) [Field K] [NumberField K] :
    NK.GlobalCFTdeep.TakagiExistence.{0, 0} K :=
  takagiExistence_of (takagiKeyCase_of_fundamentalClass hFC) (descent_of_fundamentalClass hFC) K

/-- **Takagi's existence theorem** (the requested statement): every open subgroup of finite index of
the idèle class group `C[K]` contains the norm group `N_{L/K}C_L` of a finite abelian extension
`L/K` of `K`.

**This is now proved unconditionally, and is axiom-clean.**  The proof is
`takagiExistence_of_fundamentalClass` applied to `NK.CFTLib.fundamentalClassElement`, the global
fundamental class (`H²(Gal(L/K), C_L) ∋` an element of order `[L:K]`), which is proved on disk in
`Submission/Work/CFTLib/fundamentalClassElement.lean` from

* `NK.GFC.fundamentalClassElement_of_cyclotomicTower` — the cohomological assembly of Milne,
  *CFT*, VIII.4.7 (proved), and
* `NK.GFC.normImage_of_auxiliary_cyclotomic` — the arithmetic input `C_K ⊆ N_{E/L₀}C_E` for the
  auxiliary tower, proved from the *cyclotomic* case of the reciprocity law
  (`NK.CFTLib.ARL.artinReciprocity_cyclotomic`, available unconditionally) (proved).

Every other link of the chain is likewise proved and axiom-clean:

* the induction on the index `main_aux` (this file);
* the key case `takagiKeyCase_of_fundamentalClass` (this file), through
  `NK.NUV2.ArtinBridge.kummerKeyCaseHerbrand` (Milne, *CFT*, Lemma 9.3);
* the descent `descent_of_fundamentalClass` (this file), through
  `NK.NUV2.ArtinBridge.normLimitation` (Milne, *CFT*, Theorem 4.8, the Norm Limitation Theorem);
* the index-`p` reduction `NK.NUV2.ArtinBridge.exists_le_index_eq_prime` and the openness of norm
  preimages `NK.NUV2.ArtinBridge.isOpen_comap_normClassHom`.

See `NOTES_takagiExistence.md` in this directory. -/
theorem takagiExistence (K : Type) [Field K] [NumberField K] :
    NK.GlobalCFTdeep.TakagiExistence.{0, 0} K :=
  takagiExistence_of_fundamentalClass NK.CFTLib.fundamentalClassElement K

end NK.NUV2.ArtinBridge
