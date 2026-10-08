/- Ported (gw_stage, 2026-10-08) from the lead design file `Submission/Work/_design_gw/Core27.lean`;
   content unchanged except this header. Namespace `Work.GW2.C27`. -/
/-
GW design pass 27 (lead), area CORE4: the §4 (12) amalgam count `Counting.PerXAmalgamCount`
(route L leaf #4, `Case2CountImpl9`) and a source check of `CORE4/EightTrich9`.

Source (Bender 1981, p. 227, page image `pg-12.png` — the OCR is WRONG at the key place):

    "Take any subgroup Y of X × E^g not lying in M, i.e., A ⊄ D := C_{PE}(Y)."

`D` is the centralizer of `Y` in the FIRST copy `W = P × E`, not in `X × E^g` (the transcription
problem of `NOTES_CASE2COUNTIMPL9D.md` §4 is resolved by the page image).

What Bender's two displays are, and why they are NOT fusion data:

* `M^g ∩ P×E = N_{PE}(X) = PKS₀ = C_{PE}(A)` is internal to the direct product `W = P × E`:
  `X ≤ A = P × K_p` is a "diagonal" (`X ≠ P`, `X ≠ K_p`), and `e ∈ E` normalizes a diagonal iff it
  centralizes its projection `K_p`.  `M ∩ X × E^g = C_{XE^g}(A)` is the same fact in the copy
  `W^g = X × E^g`, using `P ≤ A = A^g` (`Case2AmalgamSetup`, PROVED).  Bender uses them only to get
  `N_D(X) ≤ C(X)`.
* "`N_D(X)` has a normal complement `Q` with `|Q| ∣ q`" is a statement about the subgroup
  `π(D) ≤ E ≅ L₂(q)` (`π : W → E`, injective on `D` because `D ∩ P = 1`): a subgroup of `L₂(q)`
  in which the order-`p` subgroup `T₀ = K_p` is Sylow and self-centralizing in its normalizer.
  This is a single-copy `L₂(q)` fact (a piece of Dickson), NOT in the bundle: it is the new input
  `L2pLocalProp` below (GAP: `Core27_l2plocal.g`, all subgroups of `PSL(2,q)`, `q ≤ 121`, 0 fails).
* `|Q| = 4` is excluded by `C_G(V) ≤ M` for four-groups `V ≤ E` — derivable from the context:
  `FourCentProp` below (route in its docstring).

The count is then a double count (`card_mul_le_card_mul`), PROVED below:
every bad `Y` has `≥ 2p` partners `Z = X^c` (`c` in one of the `≤ 2` Sylow `r`-subgroups `R ≤ E`
normalized by `K_p`), there are `≤ 2(q−1)` such `Z`, and each `Z` has `≤ q − 1` bad partners
(the symmetric argument in the copy `W^g`).  Hence `#SII · 2p ≤ 2(q−1)²`, i.e. `#SII ≤ (q−1)q/p`.
So `Counting.PerXAmalgamCount` is TRUE AS STATED; it was under-hypothesised only by the missing
`L₂(q)` input.
-/
import Mathlib
import Submission.Work.CORE4.Counting.PerXAmalgamCount
import Submission.Work.CORE4.EightIdxDefs
import Submission.Work.CORE4.BadCountInH
import Submission.Work.CORE4.Case2EightQfacts
import Submission.Work.CORE4Qsub.A_le_pCoreInU

open scoped MatrixGroups

namespace Work.GW2.C27

open Work.GW2 Work.CORE4 Subgroup

/-! ## 1. The new `L₂(q)` input (single copy, no fusion) -/

/-- **NEW INPUT (L2F-style, single copy).**  Let `E ≅ L₂(r^e)` (`r` odd), `p` an odd prime,
`p ≠ r`, `T ≤ H ≤ E` with `|T| = p`, `p² ∤ |H|` (so `T` is Sylow in `H`) and `N_H(T) ≤ C(T)`.
Then either `T` is the only subgroup of order `p` of `H`, or `H` contains a four-group, or there
is a Sylow `r`-subgroup `R` of `E` normalized by `T` such that every order-`p` subgroup of `H` is
`T^c` with `c ∈ R ∩ H`.

GAP: `_design_gw/Core27_l2plocal.g` → `Core27_l2plocal.out`: every subgroup class `H` of
`PSL(2,q)`, `q ∈ {5,…,61,81,121}`, every odd prime `p ≠ r` — 0 failures; in the `R`-case
`n_p(H)` is a power of `r`, `≡ 1 (mod 2p)`, `≤ q`.

Route (no Dickson; uses only proved `l2*` facts + Mathlib):
1. Burnside (`MonoidHom.ker_transferSylow_isComplement'`; `T` abelian Sylow, `N_H(T) ≤ C(T)`):
   `H` has a normal `p`-complement `Q`, so the order-`p` subgroups of `H` are `T^c`, `c ∈ Q`.
2. For each prime `ℓ ∣ |Q|`, `T` fixes a Sylow `ℓ`-subgroup `Q_ℓ` of `Q` (`T` acts on
   `Syl_ℓ(Q)`, whose size divides `|Q|`, prime to `p`: `IsPGroup.card_modEq_card_fixedPoints`).
3. `ℓ` odd, `ℓ ≠ r`: `Q_ℓ` is cyclic and `T ≤ N(Ω₁ Q_ℓ)`, a dihedral group whose rotation part is
   `C(Ω₁ Q_ℓ)` (`l2torusNorm`); `T` has odd order, so `T ≤ C(Ω₁ Q_ℓ)` (cyclic) and `[T,Q_ℓ] = 1`.
   `ℓ = 2`: if `[T,Q₂] ≠ 1` then `Ω₁(Z(Q₂))` is a four-group (else `T ≤ C(u)`, dihedral by
   `l2cent`, and a reflection in `Q₂` would force `T ≤ Q₂`).
4. `C_Q(T) ≤ C_E(T)`, a cyclic group of order `(q±1)/2`, prime to `r`; by 3 it contains a Sylow
   `ℓ`-subgroup of `Q` for every `ℓ ≠ r`.  So `Q = Q_r · C_Q(T)` and `T^Q = T^{Q_r}`.
5. `Q_r ≤ R ∈ Syl_r(E)` and, if `Q_r ≠ 1`, `T ≤ N(R)` (Sylow `r`-subgroups are TI: `l2ti`). -/
def L2pLocalProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (E : Subgroup G) (r e : ℕ) [Fact r.Prime], Odd r →
    5 ≤ r ^ e → Nonempty (E ≃* PSL(2, GaloisField r e)) →
    ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ r →
    ∀ T H : Subgroup G, T ≤ H → H ≤ E → Nat.card T = p → ¬ p ^ 2 ∣ Nat.card H →
      H ⊓ normalizer (T : Set G) ≤ centralizer (T : Set G) →
      (∀ Z : Subgroup G, Z ≤ H → Nat.card Z = p → Z = T) ∨
      (∃ V : Subgroup G, V ≤ H ∧ IsFourGroup V) ∨
      (∃ R : Subgroup G, R ≤ E ∧ Nat.card R = r ^ e ∧ T ≤ normalizer (R : Set G) ∧
        ∀ Z : Subgroup G, Z ≤ H → Nat.card Z = p → ∃ c ∈ R ⊓ H, Z = conjSub c T)

/-! ## 2. The context lemma excluding `|Q| = 4` -/

/-- **LEAF `FourCent`** (Bender p. 227: "`|Q| = 4` would imply `C_G(Q) ⊆ M` because
`C_G(⟨t,s⟩) = ⟨t,s⟩B ⊆ M` and `s` now is an arbitrary element of `S − S₀`").

Route.  `V^e ≤ S` for some `e ∈ E` (`S ≤ E` by `nine`, Sylow); a four-group of the dihedral `S`
contains `t` (`|S| = 4`: `V^e = S`; `|S| ≥ 8`: `t` generates `Z(S)`), so `V^e = ⟨t, s'⟩` with
`s' ∈ S ∖ S₀`, i.e. `s' = s z`, `z ∈ S₀`.  `Y^e ≤ C(t) = H = U S` (`I.toolkit.split`) has odd
order, so `Y^e ≤ C_U(s')`.  Now `C_U(s') ≤ M`: `z` centralizes `U` (`Case2S0_comm_U`), so `s'`
inverts `K` like `s`; hence `C_{F(U)}(s') ∩ M = C_{K₀F}(s') = F` (`SixThree`), and
`F' := C_{F(U)}(s') ≥ F` is nilpotent with `N_{F'}(F) ≤ N_G(F) ∩ F' = F` (`normalizer F = M`),
so `F' = F` and `C_U(s') ≤ N_G(F') = M`.  Finally `Y ≤ M^{e⁻¹} = M`. -/
def FourCentProp (I : C4Inputs) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], BenderCtx G → ∀ (B : BenderSetup G) (h : Case2Ctx B),
    Case2 B → Case2PrePlus B h.D → Case2SevenFacts B h.D →
    ∀ V : Subgroup G, V ≤ layerIn h.D.M → IsFourGroup V →
    ∀ Y : Subgroup G, Odd (Nat.card Y) → Y ≤ centralizer (V : Set G) → Y ≤ h.D.M

/-! ## 3. The copy lemma (used twice: in `W = P × E` and in `W^g = X × E^g`) -/

/-- **LEAF `CopyLocal`** (pure, generic — no Bender context).  `W₀ = P₀ × E₀` (`P₀` of order `p`
central, `E₀ ≅ L₂(q)`), `T₀ ≤ E₀` of order `p` with cyclic `C_{E₀}(T₀)`, `X₁` a diagonal of
`P₀ × T₀`, and `Y` (order `p`) centralizing `X₁` but not `P₀`, such that `Y` centralizes no
four-group of `E₀` unless it normalizes `P₀`.  Then the order-`p` subgroups of
`D := C_{W₀}(Y)` are `X₁` only, or they are `X₁^c` for `c` in one Sylow `r`-subgroup `R` of `E₀`
normalized by `T₀`, and their number is `≡ 1 (mod 2p)` and `≤ q`.

Route.  `D ∩ P₀ = 1` (`|P₀| = p`, `¬ P₀ ≤ C(Y)`); `H := (D ⊔ P₀) ⊓ E₀ = π(D)`; `T₀ ≤ H`
(`T₀ ≤ X₁ ⊔ P₀`).  `N_{W₀}(X₁) = P₀ × C_{E₀}(T₀)` (a diagonal is normalized by `e ∈ E₀` iff `e`
centralizes its projection), hence `N_H(T₀) ≤ C(T₀)`; and `p ∤ |C_{E₀}(T₀) ∩ C(Y)|` (else the
unique order-`p` subgroup `T₀` of the cyclic `C_{E₀}(T₀)` centralizes `Y`, so `P₀ ≤ X₁T₀ ≤ C(Y)`),
so `X₁` is Sylow in `D` and `p² ∤ |H|`.  Apply `L2pLocalProp`.  Four-group case: a 2-element
`v ∈ H` lies in `D` (`(av)^{ord v} = a^{ord v} ∈ D ∩ P₀ = 1`), so `Y ≤ C(V)`, `Y ≤ N(P₀)`, and an
order-`p` group normalizing an order-`p` group centralizes it — contradiction.  `R`-case: each
`c ∈ R ∩ H` lies in `D` (same argument), and `π` is injective on `D`, so the order-`p` subgroups of
`D` are the `X₁^c`, `c ∈ R ∩ H`: an `R ∩ H`-orbit (size `∣ r^e`, odd) which is `Syl_p(D)`
(size `≡ 1 mod p`, Mathlib `card_sylow_modEq_one`). -/
def CopyLocalProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (P₀ E₀ T₀ X₁ Y : Subgroup G) (p r e : ℕ) [Fact r.Prime],
    Odd r → 5 ≤ r ^ e → Nonempty (E₀ ≃* PSL(2, GaloisField r e)) →
    p.Prime → p ≠ 2 → p ≠ r →
    Nat.card P₀ = p → P₀ ≤ centralizer (E₀ : Set G) → P₀ ⊓ E₀ = ⊥ →
    T₀ ≤ E₀ → Nat.card T₀ = p → IsCyclic ↥(E₀ ⊓ centralizer (T₀ : Set G)) →
    X₁ ≤ P₀ ⊔ T₀ → Nat.card X₁ = p → X₁ ≠ P₀ → X₁ ≠ T₀ →
    Nat.card Y = p → Y ≤ centralizer (X₁ : Set G) → ¬ P₀ ≤ centralizer (Y : Set G) →
    (∀ V : Subgroup G, V ≤ E₀ → IsFourGroup V → Y ≤ centralizer (V : Set G) →
        Y ≤ normalizer (P₀ : Set G)) →
    ({Z : Subgroup G | Z ≤ (P₀ ⊔ E₀) ⊓ centralizer (Y : Set G) ∧ Nat.card Z = p} = {X₁}) ∨
    (∃ R : Subgroup G, R ≤ E₀ ∧ Nat.card R = r ^ e ∧ T₀ ≤ normalizer (R : Set G) ∧
      (∀ Z : Subgroup G, Z ≤ (P₀ ⊔ E₀) ⊓ centralizer (Y : Set G) → Nat.card Z = p →
          ∃ c ∈ R, Z = conjSub c X₁) ∧
      {Z : Subgroup G | Z ≤ (P₀ ⊔ E₀) ⊓ centralizer (Y : Set G) ∧ Nat.card Z = p}.ncard
          % (2 * p) = 1 ∧
      {Z : Subgroup G | Z ≤ (P₀ ⊔ E₀) ⊓ centralizer (Y : Set G) ∧ Nat.card Z = p}.ncard
          ≤ r ^ e)

/-! ## 4. The objects of p. 227 and the three counting leaves -/

section Objects
variable {G : Type} [Group G]

/-- Bender's bad set (`Counting.PerXAmalgamCount`'s set, verbatim): conjugates `Y` of `P` in the
copy `W^g = X × E^g`, not in `𝓓`, centralizing some `Z ∈ 𝓓 ∖ {X}`. -/
def amalgamSII (P E : Subgroup G) (g : G) : Set (Subgroup G) :=
  {Y | (∃ Z ∈ inConjSet P E, Y = conjSub g Z) ∧ Y ∉ inConjSet P E ∧
    ∃ Z ∈ inConjSet P E, Z ≠ conjSub g P ∧ Y ≤ centralizer (Z : Set G)}

/-- The possible partners: `X^c ≠ X`, `c` in a subgroup `R ≤ E` of order `q` normalized by
`K_p = A ⊓ K` (there are `≤ 2` such `R`: `L2NormTwoE`). -/
def amalgamWit (E Kp X : Subgroup G) (q : ℕ) : Set (Subgroup G) :=
  {Z | Z ≠ X ∧ ∃ R : Subgroup G, R ≤ E ∧ Nat.card R = q ∧ Kp ≤ normalizer (R : Set G) ∧
    ∃ c ∈ R, Z = conjSub c X}

end Objects

/-- The hypothesis list of `Counting.PerXAmalgamCount` (minus the unused `𝓓`-count), shared by
the three leaves. -/
def AmalgamCtx (I : C4Inputs) (body : ∀ (G : Type) [Group G] [Finite G] (B : BenderSetup G),
    Case2Ctx B → ℕ → Subgroup G → Subgroup G → G → Prop) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], BenderCtx G →
    ∀ (B : BenderSetup G) (h : Case2Ctx B), Case2 B →
      Case2PrePlus B h.D → Case2SevenFacts B h.D → Case2EightAll B h.D →
      ∀ (p : ℕ) (P A : Subgroup G), p.Prime → P ≤ h.D.F → Nat.card ↥P = p →
        Case2EightObj h.D p P A →
        ∀ g : G, conjSub g P ≠ P → conjSub g P ≤ A → body G B h p P A g

/-- **LEAF `WitCard`**: `≤ 2` Sylow `r`-subgroups `R` normalized by `K_p` (`L2NormTwoE`, with
`|K_p| = p`, `p ∤ q`), each contributing `≤ q − 1` conjugates `X^c ≠ X`
(`c ↦ X^c` from `R`, and `c = 1` gives `X`). -/
def WitCardProp (I : C4Inputs) : Prop :=
  AmalgamCtx I fun G _ _ B h p P A g =>
    (amalgamWit (layerIn h.D.M) (A ⊓ h.D.K) (conjSub g P) (qOf h)).ncard ≤ 2 * (qOf h - 1)

/-- **LEAF `PerY`**: every bad `Y` has at least `2p` partners in `amalgamWit`.

Route.  `CopyLocalProp` with `(P₀,E₀,T₀,X₁) = (P, E, K_p, X)`.  Inputs: `Y ∉ 𝓓 ⇒ ¬ P ≤ C(Y)`
(notes `…9E.md` §1(2): `Y ∈ 𝓓^g`, `[Y,P] = 1` ⇒ `Y ≤ C_G(A)` ⇒ `Y ≤ A^g = A` by the copy
`key` of `BadCountInH_first`, after `WLOG g = h'`); `Y ≤ C(X)` (`X = Z(W^g)`); the four-group
hypothesis from `FourCentProp` (`M = N_G(P)`, `Case2NormalizerP`); `X ≠ K_p` (`P` is centralized
by `S`, `K_p` is inverted by `s`).  The first alternative of `CopyLocal` contradicts the witness
`Z ≠ X` of `Y ∈ SII`; in the second, `Syl_p(D) ∖ {X} ⊆ amalgamWit` and `|Syl_p(D)| ≥ 2p + 1`. -/
def PerYProp (I : C4Inputs) : Prop :=
  AmalgamCtx I fun G _ _ B h p P A g =>
    ∀ Y ∈ amalgamSII P (layerIn h.D.M) g,
      2 * p ≤ {Z | Z ∈ amalgamWit (layerIn h.D.M) (A ⊓ h.D.K) (conjSub g P) (qOf h) ∧
        Y ≤ centralizer (Z : Set G)}.ncard

/-- **LEAF `PerZ`**: every partner `Z` has at most `q − 1` bad `Y`'s.

Route.  If no bad `Y` centralizes `Z` the count is `0`.  Otherwise `[Z,X] ≠ 1` (notes `…9E.md`
§1(3)).  Replace `g` by `h' ∈ H` with `P^{h'} = X`, `A^{h'} = A` (`Case2AmalgamSetup`;
`h'⁻¹g ∈ M` preserves `𝓓`, so the bad set is unchanged).  `CopyLocalProp` in the copy:
`(P₀,E₀,T₀,X₁,Y) = (X, E^{h'}, K_p^{h'}, P, Z)` — `P ≤ A = A^{h'} = X × K_p^{h'}`, `Z ≤ W ≤ C(P)`,
`¬ X ≤ C(Z)`, four-group hypothesis = `FourCentProp` conjugated by `h'` (`N_G(X) = M^{h'}`).
A bad `Y` centralizing `Z` is an order-`p` subgroup of `C_{W^{h'}}(Z)` other than `P`
(`P ∈ 𝓓`), and there are `≤ q` of those. -/
def PerZProp (I : C4Inputs) : Prop :=
  AmalgamCtx I fun G _ _ B h p P A g =>
    ∀ Z ∈ amalgamWit (layerIn h.D.M) (A ⊓ h.D.K) (conjSub g P) (qOf h),
      {Y | Y ∈ amalgamSII P (layerIn h.D.M) g ∧ Y ≤ centralizer (Z : Set G)}.ncard ≤ qOf h - 1

/-- **`WitCard`, PROVED** (from `L2NormTwoE`, `exists_Kp_A_eq`, `p_parity_facts`). -/
theorem witCard (I : C4Inputs) : WitCardProp I := by
  intro G _ _ hbc B h _ _ _ _ p P A hp hPF hPcard hObj g _ _
  classical
  set E : Subgroup G := layerIn h.D.M with hE
  set X : Subgroup G := conjSub g P with hX
  set q : ℕ := qOf h with hq
  obtain ⟨Kp, hKpK, hKpcard, hKpomega, hAeq⟩ := Work.CORE4.exists_Kp_A_eq I h hp hPF hPcard hObj
  obtain ⟨_, hp2, hpne⟩ := Work.CORE4.p_parity_facts I hbc h hp hPF hPcard hObj
  have hAexp : ∀ x ∈ A, x ^ p = 1 := hObj.2.2.2.2.2.1
  have hAK : A ⊓ h.D.K = Kp := by
    refine le_antisymm ?_ (le_inf (hAeq ▸ le_sup_right) hKpK)
    intro x hx
    exact (hKpomega x (Subgroup.mem_inf.mp hx).2).mp (hAexp x (Subgroup.mem_inf.mp hx).1)
  have hKpE : Kp ≤ E := hKpK.trans (Work.CORE4.K_le_layerIn B h)
  set ℛ : Set (Subgroup G) :=
    {Q : Subgroup G | Q ≤ E ∧ Nat.card ↥Q = q ∧ Kp ≤ normalizer (Q : Set G)} with hℛ
  have hℛcard : ℛ.ncard ≤ 2 :=
    Work.CORE4.L2NormTwoE I G hbc B h p Kp hp hp2 hpne hKpE hKpcard
  have hℛfin : ℛ.Finite := Set.toFinite _
  let f : Subgroup G → Set (Subgroup G) :=
    fun R => ((fun c => conjSub c X) '' (R : Set G)) \ {X}
  have hsub : amalgamWit E (A ⊓ h.D.K) X q ⊆ ⋃ R ∈ hℛfin.toFinset, f R := by
    rintro Z ⟨hZX, R, hRE, hRcard, hRn, c, hc, rfl⟩
    refine Set.mem_biUnion (x := R) ?_ ?_
    · rw [Finset.mem_coe, Set.Finite.mem_toFinset]
      exact ⟨hRE, hRcard, hAK ▸ hRn⟩
    · exact ⟨⟨c, hc, rfl⟩, hZX⟩
  have hf : ∀ R ∈ hℛfin.toFinset, (f R).ncard ≤ q - 1 := by
    intro R hR
    rw [Set.Finite.mem_toFinset] at hR
    have hmem : X ∈ (fun c => conjSub c X) '' (R : Set G) := by
      refine ⟨1, R.one_mem, ?_⟩
      ext x
      simp [Work.GW2.conjSub]
    have hle : ((fun c => conjSub c X) '' (R : Set G)).ncard ≤ q := by
      refine (Set.ncard_image_le (Set.toFinite _)).trans (le_of_eq ?_)
      rw [← hR.2.1, ← Nat.card_coe_set_eq]
      rfl
    show (((fun c => conjSub c X) '' (R : Set G)) \ {X}).ncard ≤ q - 1
    rw [Set.ncard_diff_singleton_of_mem hmem]
    omega
  calc (amalgamWit E (A ⊓ h.D.K) X q).ncard
      ≤ (⋃ R ∈ hℛfin.toFinset, f R).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ ≤ ∑ R ∈ hℛfin.toFinset, (f R).ncard := Finset.set_ncard_biUnion_le _ _
    _ ≤ ∑ _R ∈ hℛfin.toFinset, (q - 1) := Finset.sum_le_sum hf
    _ = hℛfin.toFinset.card * (q - 1) := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ 2 * (q - 1) := by
        apply Nat.mul_le_mul_right
        rw [← Set.ncard_eq_toFinset_card ℛ hℛfin]
        exact hℛcard

/-! ## 5. PROVED: the double count, and `PerXAmalgamCount` from the three leaves -/

/-- Double counting on sets (`Finset.card_mul_le_card_mul`). -/
theorem ncard_mul_le_of_double_count {α : Type*} [Finite α] (S W : Set α) (rel : α → α → Prop)
    (m n : ℕ) (hm : ∀ y ∈ S, m ≤ {z | z ∈ W ∧ rel y z}.ncard)
    (hn : ∀ z ∈ W, {y | y ∈ S ∧ rel y z}.ncard ≤ n) :
    S.ncard * m ≤ W.ncard * n := by
  classical
  have : Fintype α := Fintype.ofFinite α
  have key := Finset.card_mul_le_card_mul (s := S.toFinset) (t := W.toFinset) rel
    (m := m) (n := n)
    (by
      intro a ha
      have := hm a (Set.mem_toFinset.mp ha)
      rw [Set.ncard_eq_toFinset_card'] at this
      convert this using 2
      ext z; simp [Finset.bipartiteAbove])
    (by
      intro b hb
      have := hn b (Set.mem_toFinset.mp hb)
      rw [Set.ncard_eq_toFinset_card'] at this
      convert this using 2
      ext y; simp [Finset.bipartiteBelow])
  simpa [Set.ncard_eq_toFinset_card'] using key

/-- The exact statement of `Work.CORE4.Counting.PerXAmalgamCount`. -/
def PerXAmalgamCountProp (I : C4Inputs) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], BenderCtx G →
    ∀ (B : BenderSetup G) (h : Case2Ctx B), Case2 B →
      Case2PrePlus B h.D → Case2SevenFacts B h.D →
      Case2EightAll B h.D →
      ∀ (p : ℕ) (P A : Subgroup G),
        p.Prime → P ≤ h.D.F → Nat.card ↥P = p → Case2EightObj h.D p P A →
        (inConjSet P (layerIn h.D.M)).ncard =
            (Case2EightP1 P A - 1) * (h.D.M ⊓ B.H).relIndex h.D.M + 1 →
        ∀ g : G, conjSub g P ≠ P → conjSub g P ≤ A →
          {Y : Subgroup G | (∃ Z ∈ inConjSet P (layerIn h.D.M),
                Y = conjSub g Z) ∧
              Y ∉ inConjSet P (layerIn h.D.M) ∧
              ∃ Z ∈ inConjSet P (layerIn h.D.M),
                Z ≠ conjSub g P ∧ Y ≤ Subgroup.centralizer (Z : Set G)}.ncard ≤
            ((qOf h - 1) * qOf h) / p

/-- Sanity: the def is the leaf's statement. -/
example (I : C4Inputs) : PerXAmalgamCountProp I := Work.CORE4.Counting.PerXAmalgamCount I

/-- **PROVED ASSEMBLY.**  `Counting.PerXAmalgamCount` from `WitCard`, `PerY`, `PerZ`. -/
theorem perXAmalgamCount_of_leaves (I : C4Inputs) (hW : WitCardProp I) (hY : PerYProp I)
    (hZ : PerZProp I) : PerXAmalgamCountProp I := by
  intro G _ _ hbc B h h2 hplus h7 h8 p P A hp hPF hPcard hObj _ g hgne hgle
  set q := qOf h with hq
  set S : Set (Subgroup G) := amalgamSII P (layerIn h.D.M) g with hS
  set W : Set (Subgroup G) := amalgamWit (layerIn h.D.M) (A ⊓ h.D.K) (conjSub g P) q with hWdef
  have hWc : W.ncard ≤ 2 * (q - 1) := hW G hbc B h h2 hplus h7 h8 p P A hp hPF hPcard hObj g hgne hgle
  have hdc : S.ncard * (2 * p) ≤ W.ncard * (q - 1) :=
    ncard_mul_le_of_double_count S W (fun Y Z => Y ≤ centralizer (Z : Set G)) (2 * p) (q - 1)
      (hY G hbc B h h2 hplus h7 h8 p P A hp hPF hPcard hObj g hgne hgle)
      (hZ G hbc B h h2 hplus h7 h8 p P A hp hPF hPcard hObj g hgne hgle)
  have hp0 : 0 < p := hp.pos
  have h1 : S.ncard * (2 * p) ≤ 2 * (q - 1) * (q - 1) :=
    hdc.trans (Nat.mul_le_mul_right _ hWc)
  have h2' : S.ncard * p ≤ (q - 1) * q := by
    have h3 : S.ncard * p ≤ (q - 1) * (q - 1) := by
      have : 2 * (S.ncard * p) ≤ 2 * ((q - 1) * (q - 1)) := by
        calc 2 * (S.ncard * p) = S.ncard * (2 * p) := by ring
          _ ≤ 2 * (q - 1) * (q - 1) := h1
          _ = 2 * ((q - 1) * (q - 1)) := by ring
      omega
    exact h3.trans (Nat.mul_le_mul_left _ (Nat.sub_le q 1))
  exact (Nat.le_div_iff_mul_le hp0).mpr h2'

/-- **PROVED TOP COMPOSITION** of the count: `Counting.PerXAmalgamCount` from the new `L₂(q)`
input and the four CORE4 leaves (`WitCard` is proved above).  To close route L leaf #4,
`Case2CountImpl9.lean` must take the amalgam bound as a hypothesis
(`Case2CountImpl9_of_amalgam (I) (hAm : PerXAmalgamCountProp I) : Case2CountImpl9 I` — its body is
the present one with `Counting.PerXAmalgamCount I` replaced by `hAm`), and `Final3` gains the
hypothesis `hL2 : L2pLocalProp` (an `L2F`-type input, discharged at staging like `l2normTwo`). -/
theorem perXAmalgamCount_of_design27 (I : C4Inputs) (hL2 : L2pLocalProp)
    (hCopy : L2pLocalProp → CopyLocalProp) (hFour : FourCentProp I)
    (hY : CopyLocalProp → FourCentProp I → PerYProp I)
    (hZ : CopyLocalProp → FourCentProp I → PerZProp I) : PerXAmalgamCountProp I :=
  perXAmalgamCount_of_leaves I (witCard I) (hY (hCopy hL2) hFour) (hZ (hCopy hL2) hFour)

/-! ## 6. `EightTrich9`: the source check

Bender p. 226: "With `Q := Ω₁(Z₂(O_p(U)))`, a non-cyclic subgroup of exponent `p`, either `A = Q`,
or `Z(Q) ⊂ A ⊂ Q` and `|Q : A| = p`, or `s` inverts `Q`."  No proof is printed; it follows from
two context facts and one pure `p`-group lemma, so `CORE4/EightTrich9` IS provable as stated
(earlier "under-hypothesised" verdicts missed `C_Q(P) ≤ N_G(P) = M`):

* (Cs) `C_Q(s) ≤ P`: `C_Q(s) ≤ U ∩ C(s) ∩ F(U) = B₀ ∩ F(U) = F` (`pre`, `F_def`, `Qfacts`), of
  exponent `p` in the cyclic `F`, whose unique order-`p` subgroup is `P`.
* (CP) `C_Q(P) ≤ A`: `C_Q(P) ≤ N_G(P) = M` (`F_ti` + `F_cyclic`, as in `Case2NormalizerP`), so
  `C_Q(P) ≤ F(U) ∩ M = K₀F` (`SixThree`), of exponent `p`, hence `≤ Ω₁(F K₀) = A`
  (`EightAeqOmegaCtx6_c4`).
* Case `C_Q(s) = 1`: `x ↦ s x s⁻¹` is a fixed-point-free involutive automorphism of `Q`
  (`s ∈ H` normalizes `U`, hence `Q`), so `s` inverts `Q`
  (`MonoidHom.FixedPointFree.coe_eq_inv_of_involutive`).
* Case `C_Q(s) ≠ 1`: then `P = C_Q(s) ≤ Q`, and `TrichCoreProp` (below) gives `Q ≤ A` or the
  second disjunct.  `Q ≤ A` forces `Q = A` (`Q` non-cyclic of exponent `p`: `|Q| ≥ p² = |A|`), so
  `U ≤ N(Q) = N(A)` (`Case2EightQfacts`), contradicting `¬ U ≤ N_G(A)`. -/

/-- **Pure `p`-group lemma for `EightTrich9`.**  `Q = Ω₁(Z₂(R))` (`R` a `p`-group), `P ≤ Q ∩ A`,
`|P| = p`, `|A| = p²`, `C_Q(P) ≤ A`.  Then `Q ≤ A`, or `A ≤ Q`, `Z(Q) < A < Q`, `|Q : A| = p`.

Proof: `Q` has class `≤ 2` (`[Q,Q] ≤ [Z₂R, R] ≤ Z(R) ∩ Q ≤ Z(Q)`).  If `P ≤ Z(Q)`,
`Q = C_Q(P) ≤ A`.  Else `Z(Q)P ≤ C_Q(P) ≤ A` with `Z(Q) ∩ P = 1`, `Z(Q) ≠ 1`, so `|Z(Q)| = p` and
`C_Q(P) = A = Z(Q)P`; `y ↦ [x,y]` (`P = ⟨x⟩`) is a homomorphism `Q → Z(Q)` with kernel `C_Q(x)`,
so `|Q : A| = p`.  GAP: `_design_gw/Core27_trich.g` (all groups of order `3³…3⁵`, `5³`, `5⁴`, `7³`,
every `(P, A)`: 336 configurations, 0 failures). -/
def TrichCoreProp : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (R P A : Subgroup G), p.Prime → p ≠ 2 →
    IsPGroup p R → P ≤ omega1 p (z2 R) → P ≤ A → A ≤ R → Nat.card P = p → Nat.card A = p ^ 2 →
    (∀ x ∈ A, x ^ p = 1) →
    omega1 p (z2 R) ⊓ centralizer (P : Set G) ≤ A →
    omega1 p (z2 R) ≤ A ∨
      (A ≤ omega1 p (z2 R) ∧ centerIn (omega1 p (z2 R)) < A ∧ A < omega1 p (z2 R) ∧
        A.relIndex (omega1 p (z2 R)) = p)

/-- `Qsub p B` is `Ω₁(Z₂(O_p(U)))` by definition, so `TrichCoreProp` applies with `R = O_p(U)`. -/
example {G : Type} [Group G] [Finite G] (p : ℕ) (B : BenderSetup G) :
    Qsub p B = omega1 p (z2 (pCoreIn p B.U)) := rfl

/-- **LEAF `TrichCs`** (Ctx6 level): `s` normalizes `Q`, and `C_Q(s) ≤ P`.
Route: `s ∈ S ≤ H` normalizes `U` (`U = O(H)` characteristic), hence `O_p(U)`, `Z₂`, `Ω₁`; and
`C_Q(s) ≤ U ∩ C(s) ∩ F(U) = B₀ ∩ F(U) = F` (`pre`: `B₀ = U ∩ C(s)`; `F_def`; `Q ≤ F(U)`), of exponent
`p` inside the cyclic `F` (`F_cyclic`), whose unique subgroup of order `p` is `P`. -/
def TrichCsProp (I : C4Inputs) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], BenderCtx G → ∀ B : BenderSetup G,
    Case2 B → ∀ C : Case2Ctx6 B, Case2PrePlus B C.D → Case2SevenFacts B C.D →
    ∀ (p : ℕ) (P A : Subgroup G), p.Prime → P ≤ C.D.F → Nat.card P = p →
      Case2EightObj C.D p P A →
      C.D.s ∈ normalizer ((Qsub p B : Subgroup G) : Set G) ∧
        ∀ x ∈ Qsub p B, C.D.s * x * C.D.s⁻¹ = x → x ∈ P

/-- **LEAF `TrichCP`** (Ctx6 level): `C_Q(P) ≤ A`.
Route: `C_Q(P) ≤ N_G(P) = M` (from `F_ti`, `F_cyclic`: the proof of `Case2NormalizerP` only uses
these), so `C_Q(P) ≤ F(U) ∩ M = (F(U) ∩ K) ⊔ F` (`SixThree`), whose elements of order `∣ p`
generate `Ω₁(F ⊔ K₀) = A` (`EightAeqOmegaCtx6_c4`; `F(U) ∩ K = K₀`). -/
def TrichCPProp (I : C4Inputs) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], BenderCtx G → ∀ B : BenderSetup G,
    Case2 B → ∀ C : Case2Ctx6 B, Case2PrePlus B C.D → Case2SevenFacts B C.D →
    ∀ (p : ℕ) (P A : Subgroup G), p.Prime → P ≤ C.D.F → Nat.card P = p →
      Case2EightObj C.D p P A →
      Qsub p B ⊓ centralizer (P : Set G) ≤ A

/-- The exact statement of `Work.CORE4.EightTrich9`. -/
def EightTrich9Prop (I : C4Inputs) : Prop :=
  ∀ (G : Type) [Group G] [Finite G], BenderCtx G → ∀ B : BenderSetup G,
    Case2 B → ∀ C : Case2Ctx6 B, Case2PrePlus B C.D → Case2SevenFacts B C.D →
    ∀ (p : ℕ) (P A : Subgroup G), p.Prime → P ≤ C.D.F → Nat.card P = p →
      Case2EightObj C.D p P A →
      ¬ B.U ≤ normalizer (A : Set G) →
      ((∀ x ∈ Qsub p B, C.D.s * x * C.D.s⁻¹ = x⁻¹) ∨
        (A ≤ Qsub p B ∧ centerIn (Qsub p B) < A ∧ A < Qsub p B ∧ A.relIndex (Qsub p B) = p))

/-- **PROVED ASSEMBLY**: `EightTrich9` from `TrichCore` (pure), `TrichCs`, `TrichCP` and the
proved `Case2EightQfacts`, `A_le_pCoreInU`. -/
theorem eightTrich9_of_leaves (I : C4Inputs) (hcore : TrichCoreProp) (hCs : TrichCsProp I)
    (hCP : TrichCPProp I) : EightTrich9Prop I := by
  intro G _ _ hbc B h2 C hplus h7 p P A hp hPF hPcard hObj hnotN
  classical
  obtain ⟨_, hUQ, _, hQnc⟩ :=
    Work.CORE4.Case2EightQfacts I G hbc B h2 C hplus h7 p P A hp hPF hPcard hObj
  obtain ⟨hAle, -, hpodd, hRp⟩ :=
    Work.CORE4Qsub.A_le_pCoreInU I G hbc B h2 C hplus h7 p P A hp hPF hPcard hObj
  obtain ⟨hsN, hCs'⟩ := hCs G hbc B h2 C hplus h7 p P A hp hPF hPcard hObj
  have hcp := hCP G hbc B h2 C hplus h7 p P A hp hPF hPcard hObj
  have hAcard : Nat.card ↥A = p ^ 2 := hObj.2.2.2.2.1
  have hAexp : ∀ x ∈ A, x ^ p = 1 := hObj.2.2.2.2.2.1
  have hPA : P ≤ A := hObj.2.2.2.2.2.2.1
  have hp2 : p ≠ 2 := by
    rintro rfl; exact absurd hpodd (by decide)
  by_cases hfix : ∃ x ∈ Qsub p B, x ≠ 1 ∧ C.D.s * x * C.D.s⁻¹ = x
  · obtain ⟨x, hxQ, hx1, hxs⟩ := hfix
    have hxP : x ∈ P := hCs' x hxQ hxs
    have hzp : Subgroup.zpowers x = P := by
      haveI : Fact p.Prime := ⟨hp⟩
      have hord : orderOf x = p := by
        have hdvd : orderOf x ∣ p := hPcard ▸ Subgroup.orderOf_dvd_natCard P hxP
        rcases hp.eq_one_or_self_of_dvd _ hdvd with h1 | h1
        · exact absurd (orderOf_eq_one_iff.mp h1) hx1
        · exact h1
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxP) ?_
      rw [hPcard, Nat.card_zpowers, hord]
    have hPQ : P ≤ Qsub p B := hzp ▸ Subgroup.zpowers_le.mpr hxQ
    rcases hcore G p (pCoreIn p B.U) P A hp hp2 hRp hPQ hPA hAle hPcard hAcard hAexp hcp with
      hQA | h2'
    · exfalso
      have hdvd : Nat.card ↥(Qsub p B) ∣ p ^ 2 := hAcard ▸ Subgroup.card_dvd_of_le hQA
      obtain ⟨k, hk, hkc⟩ := (Nat.dvd_prime_pow hp).mp hdvd
      interval_cases k
      · apply hQnc
        rw [pow_zero, Subgroup.card_eq_one] at hkc
        rw [hkc]; exact isCyclic_of_subsingleton
      · apply hQnc
        haveI : Fact p.Prime := ⟨hp⟩
        rw [pow_one] at hkc
        exact isCyclic_of_prime_card hkc
      · have hQeq : Qsub p B = A := Subgroup.eq_of_le_of_card_ge hQA (by rw [hkc, hAcard])
        exact hnotN (hQeq ▸ hUQ)
    · exact Or.inr h2'
  · left
    push_neg at hfix
    have hs2 : C.D.s * C.D.s = 1 := by
      have := pow_orderOf_eq_one C.D.s
      rw [C.D.s_order, pow_two] at this
      exact this
    have hsinv : C.D.s⁻¹ = C.D.s := inv_eq_of_mul_eq_one_right hs2
    let φ : ↥(Qsub p B) →* ↥(Qsub p B) :=
      { toFun := fun y => ⟨C.D.s * y * C.D.s⁻¹,
          (Subgroup.mem_normalizer_iff.mp hsN (y : G)).mp y.2⟩
        map_one' := by ext; simp
        map_mul' := by intro a b; ext; simp only [Subgroup.coe_mul]; group }
    have hfpf : MonoidHom.FixedPointFree φ := by
      intro y hy
      by_contra hy1
      have hy' : C.D.s * (y : G) * C.D.s⁻¹ = (y : G) := congrArg Subtype.val hy
      exact hfix (y : G) y.2 (fun h => hy1 (Subtype.ext h)) hy'
    have hinvol : Function.Involutive φ := by
      intro y
      ext
      show C.D.s * (C.D.s * (y : G) * C.D.s⁻¹) * C.D.s⁻¹ = (y : G)
      rw [hsinv]
      calc C.D.s * (C.D.s * (y : G) * C.D.s) * C.D.s
          = (C.D.s * C.D.s) * (y : G) * (C.D.s * C.D.s) := by group
        _ = (y : G) := by rw [hs2, one_mul, mul_one]
    have hφ := MonoidHom.FixedPointFree.coe_eq_inv_of_involutive hfpf hinvol
    intro x hx
    have := congrFun hφ ⟨x, hx⟩
    exact congrArg Subtype.val this

-- `EightTrich9Prop` is copied verbatim from `CORE4/EightTrich9.lean` (no olean yet, so no
-- `example` check here); once it builds: `example (I) : EightTrich9Prop I := Work.CORE4.EightTrich9 I`.

end Work.GW2.C27

#print axioms Work.GW2.C27.ncard_mul_le_of_double_count
#print axioms Work.GW2.C27.witCard
#print axioms Work.GW2.C27.perXAmalgamCount_of_leaves
#print axioms Work.GW2.C27.perXAmalgamCount_of_design27
#print axioms Work.GW2.C27.eightTrich9_of_leaves
