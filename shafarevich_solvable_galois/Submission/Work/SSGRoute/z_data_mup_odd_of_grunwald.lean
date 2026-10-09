import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.z_data_mup_arith
import Submission.Work.SSGRoute.grunwald_escape_relative
import Submission.Work.SSGRoute.shafarevich_z_data_two
import Submission.Work.SSGRoute.z_data_mup_core
import Submission.Work.SSGRoute.place_basics
import Submission.Work.SSGRoute.ZSplit.FrobeniusValue
import Submission.Work.SSGRoute.ZSplit.SWFourOddKummer
import Submission.Work.SSGRoute.ZSplit.SWClauses
import Submission.Work.SSGRoute.ZSplit.exists_kummerCocharZMod_of_additive_locConst
import Submission.Work.SSGRoute.ZDataMup.swOddStep
import Submission.Work.SSGRoute.ZDataMup.sw_odd_kummer_core
import Submission.Work.SSGRoute.GrunwaldEscapeCore.escape_realisation_core
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

/-! ## The recursion step of the §4 construction (the `Nat.rec` step)

Schmidt–Wingberg build a sequence `z_1, z_2, …` by applying the realisation oracle at the growing
place set `T_n = cs(S) ∪ {the blocks of P_1, …, P_{n-1}}`, with the local datum `½y` at the places
above the primes of `S` and the *corrections* `-(z_j)` at the block of the `j`-th escape prime
(`j < n`).  The lemma below is that step, isolated from the (purely combinatorial) bookkeeping of the
place sets: given a place set `T` that contains a representative of every `K`-prime above the
`k`-primes of `S` (so that the datas of `y` at the `cs(S)`-places are covered) and that covers the
primes over `p` and the primes ramified in `N`, together with any local datum `D` on the local groups
of `T` that is additive, locally constant and either zero or supported at `N`-split places, the
oracle produces the next class `z` and its escape prime `Q`.

This is the `Nat.rec` step: the caller supplies, at stage `n`, the tuple `T` (with its block
bookkeeping) and the datum `D` (the accumulated corrections), and receives `(z, Q)`.  The shoe box
and the final Hilbert-symbol verification are separate (see
`NOTE_z_data_mup_odd_of_grunwald_state.md` §7bis). -/
theorem exists_z_step {k Ω : Type} [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) (K N : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [FiniteDimensional k N] [IsGalois k N] (hKN : K ≤ N)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (S T : Finset (ValuationSubring Ω)) (y : (Ω ≃ₐ[k] Ω) → ZMod p)
    (hy : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h)
    (hyc : SSGRoute.IsLocConstOn K.fixingSubgroup y)
    (hyS : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k N B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hTfin : ∀ A ∈ T, SSGRoute.IsFinPlace k A)
    (hTdisj : ∀ A ∈ T, ∀ B ∈ T, gesKConj K A B → A = B)
    (hTcov : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (B.valuation (p : Ω) < 1 ∨
        (∃ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ ∧ σ ∉ N.fixingSubgroup)) →
      ∃ A ∈ T, gesKConj K A B)
    (hTS : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) → ∃ A ∈ T, gesKConj K A B)
    (D : ValuationSubring Ω → (Ω ≃ₐ[k] Ω) → ZMod p)
    (hDadd : ∀ A ∈ T, ∀ x ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
      ∀ y' ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, D A (x * y') = D A x + D A y')
    (hDlc : ∀ A ∈ T, ∃ U : Subgroup (Ω ≃ₐ[k] Ω), IsOpen (U : Set (Ω ≃ₐ[k] Ω)) ∧
      ∀ x ∈ U, x ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup → D A x = 0)
    (hDorth : ∀ A ∈ T,
      (∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, D A σ = 0) ∨ SSGRoute.IsSplitIn k N A) :
    ∃ (z : (Ω ≃ₐ[k] Ω) → ZMod p) (Q : ValuationSubring Ω),
      SSGRoute.IsFinPlace k Q ∧ SSGRoute.IsSplitIn k N Q ∧
      (∀ A ∈ T, ¬ gesKConj K A Q) ∧
      (∀ x ∈ K.fixingSubgroup, ∀ y' ∈ K.fixingSubgroup, z (x * y') = z x + z y') ∧
      SSGRoute.IsLocConstOn K.fixingSubgroup z ∧
      (∀ A ∈ T, ∀ σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
        z σ = (2 : ZMod p)⁻¹ * y σ + D A σ) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ T, ¬ gesKConj K A B) → (¬ gesKConj K Q B) →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → z σ = 0) := by
  classical
  have hg : ∀ x ∈ K.fixingSubgroup, ∀ y' ∈ K.fixingSubgroup,
      (fun σ => (2 : ZMod p)⁻¹ * y σ) (x * y') =
        (fun σ => (2 : ZMod p)⁻¹ * y σ) x + (fun σ => (2 : ZMod p)⁻¹ * y σ) y' := by
    intro x hx y' hy'
    show (2 : ZMod p)⁻¹ * y (x * y') = (2 : ZMod p)⁻¹ * y x + (2 : ZMod p)⁻¹ * y y'
    rw [hy x hx y' hy', mul_add]
  have hgc : SSGRoute.IsLocConstOn K.fixingSubgroup (fun σ => (2 : ZMod p)⁻¹ * y σ) := by
    obtain ⟨U, hUo, hU⟩ := hyc
    exact ⟨U, hUo, fun g hg' u hu huH => by
      show (2 : ZMod p)⁻¹ * y (g * u) = (2 : ZMod p)⁻¹ * y g
      rw [hU g hg' u hu huH]⟩
  have hgram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ T, ¬ gesKConj K A B) → ¬ SSGRoute.IsSplitIn k N B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ →
        (fun σ => (2 : ZMod p)⁻¹ * y σ) σ = 0 := by
    intro B hB hnotT hns σ hσK hσI
    have hnotS : ∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B := by
      intro A hA hconj
      obtain ⟨A', hA'T, hconj'⟩ := hTS B hB ⟨A, hA, hconj⟩
      exact hnotT A' hA'T hconj'
    show (2 : ZMod p)⁻¹ * y σ = 0
    rw [hyS B hB hnotS hns σ hσK hσI, mul_zero]
  obtain ⟨z, Q, hQfin, hQsplit, hQnot, hzadd, hzloc, hzdat, hzunr⟩ :=
    Work.SSGRoute.GrunwaldEscapeCore.escape_realisation_core p hp k Ω K N hKN ζ hζ hζK T hTfin
      hTdisj hTcov (fun σ => (2 : ZMod p)⁻¹ * y σ) hg hgc hgram D hDadd hDlc hDorth
  exact ⟨z, Q, hQfin, hQsplit, hQnot, hzadd, hzloc, hzdat, hzunr⟩

/-! ## The inertia → decomposition upgrade

The reviewers' caveat on this node is exactly this: the realisation oracle
`grunwald_escape_relative` concludes only with *inertia* vanishing at the places outside `cs(T)` and
outside the `G_K`-conjugates of its escape prime, whereas the target's last conjunct needs vanishing
on the whole decomposition group `decomp k Q ⊓ K.fixingSubgroup` (`Q` a `k`-conjugate of a place at
which the class is ramified).  That upgrade is available on disk, in the tree's vocabulary: an
unramified class is determined on its whole local group by its value at a *Frobenius* element, once
the local group is generated by that Frobenius modulo a level kernel which the class kills
(`Work.SSGRoute.ZSplit.localValue_eq_zero_of_frob_eq_zero`, with
`Work.SSGRoute.ZSplit.hker_of_kills_inertia` producing the level-kernel hypothesis from
"kills the inertia").  The lemma below is that upgrade, stated in the form in which the target's last
conjunct consumes it: it reduces the last clause of the node to the *pure Frobenius-value vanishing*
`hval` (which is what Schmidt–Wingberg's Hilbert-symbol computation of pp. 15–16 supplies).
-/

/-- **The inertia → decomposition upgrade.**  If `z` is additive on `G_K`, kills the inertia of a
finite place `A`, and vanishes at an element `σ ∈ decomp k A ⊓ G_K` which generates the local group
modulo a level `L` whose kernel is inertia (`hLI`) and which `z` kills, then `z` vanishes on the
*whole* local group `decomp k A ⊓ K.fixingSubgroup`. -/
theorem kills_localGroup_of_kills_inertia_and_frob {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] {p : ℕ} [Fact p.Prime] (K L : IntermediateField k Ω)
    [FiniteDimensional k K] [IsGalois k K] [FiniteDimensional k L] [IsGalois k L]
    (A : ValuationSubring Ω) (z : (Ω ≃ₐ[k] Ω) → ZMod p)
    (hz : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, z (g * h) = z g + z h)
    (σ : Ω ≃ₐ[k] Ω) (hσ : σ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup)
    (hLI : ∀ u ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup,
      SSGRoute.res k L u = 1 → SSGRoute.IsInertia k A u)
    (hpow : ∀ τ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, ∃ m : ℤ,
      SSGRoute.res k L τ = (SSGRoute.res k L σ) ^ m)
    (hzI : ∀ u ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, SSGRoute.IsInertia k A u → z u = 0)
    (hval : z σ = 0) :
    ∀ τ ∈ SSGRoute.decomp k A ⊓ K.fixingSubgroup, z τ = 0 :=
  Work.SSGRoute.ZSplit.localValue_eq_zero_of_frob_eq_zero K L A z hz σ hσ hpow
    (Work.SSGRoute.ZSplit.hker_of_kills_inertia K L A z hLI hzI) hval

/-! ## The last clause is vacuous when the ramification outside `cs(S)` sits on a prescribed set

The target's last conjunct (Schmidt--Wingberg's `z_{σP} = 0` for `σ ≠ 1`) is the one clause that the
realisation oracle `Work.SSGRoute.grunwald_escape_relative` does **not** supply: its conclusion gives
only *inertia* vanishing outside `cs(T)` and outside the `G_K`-conjugates of its escape prime `Q`,
whereas the target needs vanishing on the whole decomposition group at the `k`-conjugates of the
places at which the class is ramified.  Schmidt--Wingberg close this gap by the Hilbert-symbol
computation of pp. 15--16 (`z = z_i + z_N`, the pigeonhole and the product formula).

The lemma below records a *structural* alternative, formalising §4 of
`NOTE_z_data_mup_odd_of_grunwald_state.md`: if the realisation can be arranged to kill the local
groups of the `k`-conjugates of a finite set `E` (for instance by prescribing the *zero* datum on the
blocks of `E`, which requires `E` to be chosen *before* the realisation and therefore needs the
escape primes to be pre-chosen), then no Hilbert symbol is needed: the last clause has no instances.
-/

/-- **The last clause of the target is automatic if `z` kills the local groups at the
`k`-conjugates of a covering set `E`.**  Hypothesis `hconf` is the confinement of the ramification of
`z`: `z` kills the inertia of every finite place outside `cs(S)` that is not `k`-conjugate to an
element of `E`; hypothesis `hkill` says that `z` kills the whole level-`K` local group of every
`k`-conjugate of every element of `E`. -/
theorem clause_six_of_killing_covering_set {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] {p : ℕ} (K N : IntermediateField k Ω) [FiniteDimensional k K]
    [IsGalois k K] [FiniteDimensional k N] [IsGalois k N]
    (S E : Finset (ValuationSubring Ω)) (z : (Ω ≃ₐ[k] Ω) → ZMod p)
    (hkill : ∀ A ∈ E, ∀ Q : ValuationSubring Ω, SSGRoute.IsConjPlace k A Q →
      ∀ τ ∈ SSGRoute.decomp k Q ⊓ K.fixingSubgroup, z τ = 0)
    (hconf : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → (∀ A ∈ E, ¬ SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → z σ = 0) :
    ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → SSGRoute.IsSplitIn k N B →
      (∃ σ, SSGRoute.IsInertia k B σ ∧ σ ∈ K.fixingSubgroup ∧ z σ ≠ 0) →
      ∀ Q : ValuationSubring Ω, SSGRoute.IsConjPlace k B Q →
        (¬ ∃ τ ∈ K.fixingSubgroup, τ • B = Q) →
        ∀ τ ∈ SSGRoute.decomp k Q ⊓ K.fixingSubgroup, z τ = 0 := by
  intro B hB hBS _ hram Q hBQ _ τ hτ
  by_contra hne
  -- `B` must be `k`-conjugate to an element of `E`: otherwise the confinement kills its inertia
  have hBE : ∃ A ∈ E, SSGRoute.IsConjPlace k A B := by
    by_contra h
    push_neg at h
    obtain ⟨σ, hσI, hσK, hσne⟩ := hram
    exact hσne (hconf B hB hBS h σ hσK hσI)
  obtain ⟨A, hAE, hAB⟩ := hBE
  exact hne (hkill A hAE Q (SSGRoute.isConjPlace_trans hAB hBQ) τ hτ)

/-! ## The involution clause is free for odd `p`: Kummer classes kill the involutions

The target's fourth conjunct asks the constructed class `z` to vanish on the involutions of `G_K`.
For the *Kummer* classes `z = χ_b` (`b ∈ Kˣ`, `ζ_p ∈ K`) this costs nothing when `p` is odd: the
Kummer index of an involution vanishes.  Indeed, if `σ ∈ G_K` satisfies `σ ^ 2 = 1` then, by the
additivity of the Kummer index,

`2 · index(σ) = index(σ²) = index(1) = 0`,

and `2` is invertible in `𝔽_p`; so `index(σ) = 0`, i.e. `σ` fixes the chosen `p`-th root of `b`.
(Equivalently: `σ(γ) = ζ^i γ` implies `γ = σ²(γ) = ζ^{2i} γ`, and `ζ^{2i} = 1` forces `i = 0`.)

This is the reason why the odd-`p` lane needs no arithmetic hypothesis for its involution clause —
in sharp contrast with `p = 2`, where the corresponding condition is "`b` totally positive at the
real places" (`Work.SSGRoute.shafarevich_z_data_two_kummerCore`). -/

/-- **For odd `p`, every level-`K` Kummer cochain kills every involution of `G_K`.** -/
theorem nodeKummerCocharZMod_involution_eq_zero {k Ω : Type} [Field k] [NumberField k] [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω] {p : ℕ} [Fact p.Prime] (hp : p ≠ 2)
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K) (β : (↥K)ˣ)
    {c : Ω ≃ₐ[k] Ω} (hc : c ∈ K.fixingSubgroup) (hc2 : c ^ 2 = 1) :
    ZSplit.nodeKummerCocharZMod K ζ hζK hζ β c = 0 := by
  have hζ' : IsPrimitiveRoot (⟨ζ, hζK⟩ : ↥K) p :=
    ZSplit.isPrimitiveRoot_subtype_of_mem_zmod hζK hζ
  have h2ne : (2 : ZMod p) ≠ 0 := by
    intro h0
    have hd : p ∣ 2 := (CharP.cast_eq_zero_iff (ZMod p) p 2).mp h0
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hd
    exact hp (le_antisymm hle (Fact.out : p.Prime).two_le)
  have hc2app : ∀ x : Ω, c (c x) = x := fun x => by
    have h := congrArg (fun (e : Ω ≃ₐ[k] Ω) => e x) hc2
    simpa using h
  have hσeq : IntermediateField.fixingSubgroupEquiv K ⟨c, hc⟩ *
      IntermediateField.fixingSubgroupEquiv K ⟨c, hc⟩ = 1 := by
    ext x
    exact hc2app x
  rw [ZSplit.nodeKummerCocharZMod_apply (K := K) (ζ := ζ) (hζK := hζK) (hζ := hζ) (β := β) hc]
  rw [kummerCharZMod_apply]
  have h2i : (2 : ZMod p) *
      (kummerIdx p hζ' β (kummerSqrtUnitZMod (Ω := Ω) p β)
        (kummerSqrtUnitZMod_pow (Ω := Ω) p β)
        (IntermediateField.fixingSubgroupEquiv K ⟨c, hc⟩)) = 0 := by
    have h := kummerIdx_mul_apply p hζ' β (kummerSqrtUnitZMod (Ω := Ω) p β)
      (kummerSqrtUnitZMod_pow (Ω := Ω) p β)
      (IntermediateField.fixingSubgroupEquiv K ⟨c, hc⟩)
      (IntermediateField.fixingSubgroupEquiv K ⟨c, hc⟩)
    rw [hσeq, kummerIdx_one p hζ' β (kummerSqrtUnitZMod (Ω := Ω) p β)
      (kummerSqrtUnitZMod_pow (Ω := Ω) p β)] at h
    rw [two_mul]
    exact h.symm
  exact (mul_eq_zero.mp h2i).resolve_left h2ne

/-! ## The Kummer cochain is additive in the element

`χ_{a b} = χ_a + χ_b` for `a, b ∈ Kˣ`; it is proved in the shared module
`Submission.Work.SSGRoute.ZDataMup.swOddStep` (imported above) as
`Work.SSGRoute.nodeKummerCocharZMod_mul`, since both this file and the arithmetic core
`Work.SSGRoute.ZDataMup.sw_odd_kummer_core` need it, and putting it here would create an import
cycle. -/

/-! ## The unramified case of the core

If `y` is unramified at *every* finite place outside `cs(S)` — a hypothesis stronger than `hyS`,
since it also forbids ramification at the places outside `cs(S)` that *are* split in `N` — then the
core is witnessed by the element `h ∈ Kˣ` whose Kummer cochain is `y` itself (Kummer theory:
every additive, locally constant cochain on `G_K` is a Kummer cochain, because `ζ_p ∈ K`,
`Work.SSGRoute.ZSplit.exists_kummerCocharZMod_of_additive_locConst`).  Indeed `χ_h = y` on all of
`G_K`, so `χ_h` is ramified exactly where `y` is, and the sharpened condition (b) has no instances
outside `cs(S)`.

This is the odd-`p` analogue of `Work.SSGRoute.shafarevich_z_data_two_kummerCore_of_unramified`, and
it is the first case of the proof of the core; the remaining case is Schmidt–Wingberg's §4
construction, where the ramification of `y` at the split places outside `cs(S)` has to be moved onto
new primes by Grünwald with escape. -/
theorem sw_odd_kummer_core_of_unramified (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K N : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k N] [IsGalois k N] [Fintype (K ≃ₐ[k] K)] (hKN : K ≤ N)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hSdisj : ∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace k A B → A = B)
    (hSram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k N B ∨ B.valuation (p : Ω) < 1) →
      ∃ A ∈ S, SSGRoute.IsConjPlace k A B)
    (y : (Ω ≃ₐ[k] Ω) → ZMod p)
    (hy : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h)
    (hyc : SSGRoute.IsLocConstOn K.fixingSubgroup y)
    (hyunr : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0) :
    ∃ b : (↥K)ˣ,
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
        ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B →
          ZSplit.nodeKummerCocharZMod K ζ hζK hζ b σ = y σ) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k N B →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ →
          ZSplit.nodeKummerCocharZMod K ζ hζK hζ b σ = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → SSGRoute.IsSplitIn k N B →
        (∃ σ, SSGRoute.IsInertia k B σ ∧ σ ∈ K.fixingSubgroup ∧
          ZSplit.nodeKummerCocharZMod K ζ hζK hζ b σ ≠ 0) →
        ∀ Q : ValuationSubring Ω, SSGRoute.IsConjPlace k B Q →
          (¬ ∃ τ ∈ K.fixingSubgroup, τ • B = Q) →
          ∀ τ ∈ SSGRoute.decomp k Q ⊓ K.fixingSubgroup,
            ZSplit.nodeKummerCocharZMod K ζ hζK hζ b τ = 0) := by
  obtain ⟨β, hβ⟩ :=
    ZSplit.exists_kummerCocharZMod_of_additive_locConst p k Ω K ζ hζK hζ y hy hyc
  refine ⟨β, ?_, ?_, ?_⟩
  · intro B hB _ σ hσK _
    exact (hβ σ hσK).symm
  · intro B hB hBS _ σ hσK hσI
    rw [← hβ σ hσK]
    exact hyunr B hB hBS σ hσK hσI
  · intro B hB hBS _ hram Q _ τ _
    obtain ⟨σ, hσI, hσK, hσne⟩ := hram
    exact absurd (hβ σ hσK ▸ hyunr B hB hBS σ hσK hσI) hσne

/-! ## The arithmetic core of the node (Smith–Wingberg §4 for odd `p` in Kummer form)

The content of the node is the existence of an element `b ∈ Kˣ` whose Kummer cochain `χ_b` realises
the prescribed local datum `y` at the places of `cs(S)`, is unramified at the places outside `cs(S)`
that are not split in `N`, and satisfies Schmidt–Wingberg's sharpened condition (b): at every place
outside `cs(S)`, split in `N`, at which `χ_b` is ramified, `χ_b` kills the local groups of all the
`k`-conjugates that are not `K`-conjugates.

This is the *only* arithmetic input of the node; it is exactly Schmidt–Wingberg's construction of
the sequence `z₁, z₂, …` (Grünwald with escape, condition (1)), the shoe box principle, and the
Hilbert-symbol computation of arXiv:math/9809211, pp. 15–16.  It is separated here so that the
node itself is a purely formal consequence of it (see
`Work.SSGRoute.z_data_mup_odd_of_grunwald_of_kummerCore` below), in the same way as the `p = 2`
lane separates `Work.SSGRoute.shafarevich_z_data_two_kummerCore`. -/
theorem sw_odd_kummer_core (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K N : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k N] [IsGalois k N] [Fintype (K ≃ₐ[k] K)] (hKN : K ≤ N)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hSdisj : ∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace k A B → A = B)
    (hSram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k N B ∨ B.valuation (p : Ω) < 1) →
      ∃ A ∈ S, SSGRoute.IsConjPlace k A B)
    (y : (Ω ≃ₐ[k] Ω) → ZMod p)
    (hy : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h)
    (hyc : SSGRoute.IsLocConstOn K.fixingSubgroup y)
    (hyS : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k N B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hyram : ∃ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B ∧
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) ∧
      ∃ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ ∧ y σ ≠ 0)
    (hyT : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hy0 : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      (¬ SSGRoute.IsSplitIn k K B ∨ B.valuation (p : Ω) < 1) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → y σ = 0)
    (hyinf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → y c = 0) :
    ∃ b : (↥K)ˣ,
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
        ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B →
          ZSplit.nodeKummerCocharZMod K ζ hζK hζ b σ = y σ) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k N B →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ →
          ZSplit.nodeKummerCocharZMod K ζ hζK hζ b σ = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → SSGRoute.IsSplitIn k N B →
        (∃ σ, SSGRoute.IsInertia k B σ ∧ σ ∈ K.fixingSubgroup ∧
          ZSplit.nodeKummerCocharZMod K ζ hζK hζ b σ ≠ 0) →
        ∀ Q : ValuationSubring Ω, SSGRoute.IsConjPlace k B Q →
          (¬ ∃ τ ∈ K.fixingSubgroup, τ • B = Q) →
          ∀ τ ∈ SSGRoute.decomp k Q ⊓ K.fixingSubgroup,
            ZSplit.nodeKummerCocharZMod K ζ hζK hζ b τ = 0) :=
  ZDataMup.sw_odd_kummer_core (p := p) (hp := hp) (k := k) (Ω := Ω) K N hKN ζ hζ hζK S hSfin
    hSdisj hSram y hy hyc hyS hyram hyT hy0 hyinf

/-- **The node follows from its Kummer core.**  Once `b ∈ Kˣ` with the three arithmetic properties
of `Work.SSGRoute.sw_odd_kummer_core` is available, the class `z := χ_b` witnesses the node: it is
additive and locally constant on `G_K` (`nodeKummerCocharZMod_add`,
`nodeKummerCocharZMod_locConst`), it agrees with `y` on `cs(S)`, it kills the involutions
(`Work.SSGRoute.nodeKummerCocharZMod_involution_eq_zero`, where `p` odd is used), and the last two
conjuncts are the core's second and third properties. -/
theorem z_data_mup_odd_of_grunwald_of_kummerCore (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (k Ω : Type)
    [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω] [IsAlgClosed Ω]
    (K N : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k N] [IsGalois k N] [Fintype (K ≃ₐ[k] K)] (hKN : K ≤ N)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hSdisj : ∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace k A B → A = B)
    (hSram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k N B ∨ B.valuation (p : Ω) < 1) →
      ∃ A ∈ S, SSGRoute.IsConjPlace k A B)
    (y : (Ω ≃ₐ[k] Ω) → ZMod p)
    (hy : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h)
    (hyc : SSGRoute.IsLocConstOn K.fixingSubgroup y)
    (hyS : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k N B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hyram : ∃ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B ∧
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) ∧
      ∃ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ ∧ y σ ≠ 0)
    (hyT : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hy0 : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      (¬ SSGRoute.IsSplitIn k K B ∨ B.valuation (p : Ω) < 1) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → y σ = 0)
    (hyinf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → y c = 0)
    (hcore : ∃ b : (↥K)ˣ,
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
        ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B →
          ZSplit.nodeKummerCocharZMod K ζ hζK hζ b σ = y σ) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k N B →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ →
          ZSplit.nodeKummerCocharZMod K ζ hζK hζ b σ = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → SSGRoute.IsSplitIn k N B →
        (∃ σ, SSGRoute.IsInertia k B σ ∧ σ ∈ K.fixingSubgroup ∧
          ZSplit.nodeKummerCocharZMod K ζ hζK hζ b σ ≠ 0) →
        ∀ Q : ValuationSubring Ω, SSGRoute.IsConjPlace k B Q →
          (¬ ∃ τ ∈ K.fixingSubgroup, τ • B = Q) →
          ∀ τ ∈ SSGRoute.decomp k Q ⊓ K.fixingSubgroup,
            ZSplit.nodeKummerCocharZMod K ζ hζK hζ b τ = 0)) :
    ∃ z : (Ω ≃ₐ[k] Ω) → ZMod p,
      (∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, z (g * h) = z g + z h) ∧
      SSGRoute.IsLocConstOn K.fixingSubgroup z ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
        ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → z σ = y σ) ∧
      (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → z c = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k N B →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → z σ = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → SSGRoute.IsSplitIn k N B →
        (∃ σ, SSGRoute.IsInertia k B σ ∧ σ ∈ K.fixingSubgroup ∧ z σ ≠ 0) →
        ∀ Q : ValuationSubring Ω, SSGRoute.IsConjPlace k B Q →
          (¬ ∃ τ ∈ K.fixingSubgroup, τ • B = Q) →
          ∀ τ ∈ SSGRoute.decomp k Q ⊓ K.fixingSubgroup, z τ = 0) := by
  haveI : IsAlgClosed Ω := (inferInstance : IsAlgClosure k Ω).isAlgClosed
  obtain ⟨b, h3, h5, h6⟩ := hcore
  refine ⟨ZSplit.nodeKummerCocharZMod K ζ hζK hζ b, ?_, ?_, h3, ?_, h5, h6⟩
  · exact ZSplit.nodeKummerCocharZMod_add K ζ hζK hζ b
  · exact ZSplit.nodeKummerCocharZMod_locConst K ζ hζK hζ b
  · intro c hc hc2
    exact nodeKummerCocharZMod_involution_eq_zero hp K ζ hζ hζK b hc hc2

/-- Schmidt-Wingberg §4 in the one-dimensional (mu_p) case, odd p, by Grunwald with escape.
Verbatim the statement of `Work.SSGRoute.sw_z_exists_odd_sketch` (`z_data_mup_arith.lean`,
lines 291-333), which is a `sorry` there (the two reviewers diffed the texts mechanically).
New route (`_NOTE_STEP4_DESIGN.md` §3, node Z2): the realisation pieces
`tatePoitou_h1_realisation_sketch` and `exists_localTateSystem_productFormula` of that file (both
`sorry`s there, to be dropped) are replaced by the pairing-free node
`Work.SSGRoute.grunwald_escape_relative` (`grunwald_escape_relative.lean`; statement = first
section of `_design_step4/StmtCheck2.lean`), applied with `L₁ := K`, `L₂ := N`, `g := y`, `T := S`
and `h` the local corrections.  Keep the pigeonhole (`Work.SSGRoute.pigeonhole_two_eq`) and the
Hilbert-symbol calculus of SW pp. 15-17 with NK's `hilbertReciprocity_cyclic`; for odd p use the NK
`UchidaKummer` dictionary as `grunwald_surjective_odd` does, and do not use
`kummerChar_eq_zero_iff_local_powClass` (a `sorry`).  The p = 2 twin
`Work.SSGRoute.shafarevich_z_data_two` (`shafarevich_z_data_two.lean`, one `sorry`) has the same
construction nearly complete and is a good template.

PROOF CAVEAT (both reviewers): the last clause of `grunwald_escape_relative` gives vanishing on
`IsInertia k B σ` at places outside `cs(T)` and outside the `K`-conjugates of its `Q`; the last
conjunct of the target demands `z τ = 0` for all `τ ∈ decomp k Q ⊓ K.fixingSubgroup`, i.e. the whole
decomposition group (Frobenius part included).  That inertia-to-decomposition upgrade is a genuine
extra step (the Kummer-element argument, as in the p = 2 proof via its `hiso`), and must not be
assumed to come for free from the Grünwald node's conclusion.

Consumed by `Work.SSGRoute.z_data_mup_core` (`z_data_mup_core.lean:150`, with `N := Λ`), hence
`Work.SSGRoute.ZConstruction.ZDataGeneral` and `SSGRoute.shafarevich_existence`. -/
theorem z_data_mup_odd_of_grunwald (p : ℕ) [Fact p.Prime] (hp : p ≠ 2) (k Ω : Type) [Field k]
    [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K N : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K]
    [FiniteDimensional k N] [IsGalois k N] [Fintype (K ≃ₐ[k] K)] (hKN : K ≤ N)
    (ζ : Ω) (hζ : IsPrimitiveRoot ζ p) (hζK : ζ ∈ K)
    (S : Finset (ValuationSubring Ω)) (hSfin : ∀ A ∈ S, SSGRoute.IsFinPlace k A)
    (hSdisj : ∀ A ∈ S, ∀ B ∈ S, SSGRoute.IsConjPlace k A B → A = B)
    (hSram : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (SSGRoute.IsRamifiedIn k N B ∨ B.valuation (p : Ω) < 1) →
      ∃ A ∈ S, SSGRoute.IsConjPlace k A B)
    (y : (Ω ≃ₐ[k] Ω) → ZMod p)
    (hy : ∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, y (g * h) = y g + y h)
    (hyc : SSGRoute.IsLocConstOn K.fixingSubgroup y)
    (hyS : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k N B →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hyram : ∃ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B ∧
      (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) ∧
      ∃ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ ∧ y σ ≠ 0)
    (hyT : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → y σ = 0)
    (hy0 : ∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
      (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
      (¬ SSGRoute.IsSplitIn k K B ∨ B.valuation (p : Ω) < 1) →
      ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → y σ = 0)
    (hyinf : ∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → y c = 0) :
    ∃ z : (Ω ≃ₐ[k] Ω) → ZMod p,
      (∀ g ∈ K.fixingSubgroup, ∀ h ∈ K.fixingSubgroup, z (g * h) = z g + z h) ∧
      SSGRoute.IsLocConstOn K.fixingSubgroup z ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∃ A ∈ S, SSGRoute.IsConjPlace k A B) →
        ∀ σ ∈ K.fixingSubgroup, σ ∈ SSGRoute.decomp k B → z σ = y σ) ∧
      (∀ c ∈ K.fixingSubgroup, c ^ 2 = 1 → z c = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → ¬ SSGRoute.IsSplitIn k N B →
        ∀ σ ∈ K.fixingSubgroup, SSGRoute.IsInertia k B σ → z σ = 0) ∧
      (∀ B : ValuationSubring Ω, SSGRoute.IsFinPlace k B →
        (∀ A ∈ S, ¬ SSGRoute.IsConjPlace k A B) → SSGRoute.IsSplitIn k N B →
        (∃ σ, SSGRoute.IsInertia k B σ ∧ σ ∈ K.fixingSubgroup ∧ z σ ≠ 0) →
        ∀ Q : ValuationSubring Ω, SSGRoute.IsConjPlace k B Q →
          (¬ ∃ τ ∈ K.fixingSubgroup, τ • B = Q) →
          ∀ τ ∈ SSGRoute.decomp k Q ⊓ K.fixingSubgroup, z τ = 0) := by
  haveI : IsAlgClosed Ω := (inferInstance : IsAlgClosure k Ω).isAlgClosed
  exact
    z_data_mup_odd_of_grunwald_of_kummerCore p hp k Ω K N hKN ζ hζ hζK S hSfin hSdisj hSram
      y hy hyc hyS hyram hyT hy0 hyinf
      (sw_odd_kummer_core p hp k Ω K N hKN ζ hζ hζK S hSfin hSdisj hSram y hy hyc hyS hyram
        hyT hy0 hyinf)

end Work.SSGRoute
