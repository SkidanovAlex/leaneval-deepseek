import Mathlib
import Submission.Work.Higman.MSA.l8_local
import Submission.Work.Higman.MSA.l8_triv
import Submission.Work.Higman.MSA.l8_BV
import Submission.Work.Higman.MSA.l8_betaV
import Submission.Work.Higman.MSA.l8_sV
import Submission.Work.Higman.MSA.l8_setup
import Submission.Work.Higman.MSA.l8_mult_core
import Submission.Work.Higman.MSA.l8_quot_irred
import Submission.Work.Higman.MSA.l8_sV_aux
import Submission.Work.Higman.MSA.l8_card_le
import Submission.Work.Higman.sq_basic
import Submission.Work.Higman.omega1_iso_field
import Submission.Work.Higman.Q3.finrank_dvd_of_irreducible_pow_sub_one

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped commutatorElement

namespace Work.Higman.MSA

open Work.Higman.MSA.L8

variable {P : Type} [Group P] [Finite P]

/-- Iterated `ξ`-equivariance of Higman's bracket `betaV`. -/
theorem betaV_xi_iter {h : IsSuzuki2Grp P} {A C : Subgroup P} [hAn : A.Normal]
    (S : D h A C) (j : ℕ) (x : ↥C ⧸ A.subgroupOf C) (w : ↥(omega1 P)) :
    betaV S (((xiQuot h S.hA.map_eq S.hCinv) ^ j) x) (((xiZ h) ^ j) w)
      = ((xiZ h) ^ j) (betaV S x w) := by
  have hβeq : ∀ (x : ↥C ⧸ A.subgroupOf C) (w : ↥(omega1 P)),
      (xiZ h) (betaV S x w) = betaV S ((xiQuot h S.hA.map_eq S.hCinv) x) ((xiZ h) w) :=
    (l8_betaV S).2.2.2.1
  induction j with
  | zero => simp
  | succ j ih =>
      calc betaV S (((xiQuot h S.hA.map_eq S.hCinv) ^ (j + 1)) x) (((xiZ h) ^ (j + 1)) w)
          = betaV S ((xiQuot h S.hA.map_eq S.hCinv)
                (((xiQuot h S.hA.map_eq S.hCinv) ^ j) x))
              ((xiZ h) (((xiZ h) ^ j) w)) := by
              rw [pow_succ', MulAut.mul_apply, pow_succ', MulAut.mul_apply]
        _ = (xiZ h) (betaV S (((xiQuot h S.hA.map_eq S.hCinv) ^ j) x) (((xiZ h) ^ j) w)) :=
              (hβeq _ _).symm
        _ = (xiZ h) (((xiZ h) ^ j) (betaV S x w)) := by rw [ih]
        _ = ((xiZ h) ^ (j + 1)) (betaV S x w) := by rw [pow_succ', MulAut.mul_apply]

/-- If a power of `ξ` is trivial on `Ω₁(P)` then it is trivial on the bracket `betaV`. -/
theorem betaV_xiZ_triv {h : IsSuzuki2Grp P} {A C : Subgroup P} [hAn : A.Normal]
    (S : D h A C) {k : ℕ} (hk : (xiZ h) ^ k = 1)
    (x : ↥C ⧸ A.subgroupOf C) (w : ↥(omega1 P)) :
    betaV S (((xiQuot h S.hA.map_eq S.hCinv) ^ k) x) w = betaV S x w := by
  have h := betaV_xi_iter S k x (((xiZ h) ^ k)⁻¹ w)
  rw [hk] at h
  simpa using h

/-- **Higman's "first step" for auxiliary result 8.**  If `ξ ^ k` acts trivially on the
`ξ`-module `Ω₁(P)`, then `ξ ^ k` acts trivially on the irreducible `ξ`-module `V = C/A`. -/
theorem l8_first_step {h : IsSuzuki2Grp P} {A C : Subgroup P} [hAn : A.Normal] (S : D h A C)
    (hirr : ∀ K : Subgroup (↥C ⧸ A.subgroupOf C),
      K.map (xiQuot h S.hA.map_eq S.hCinv).toMonoidHom = K → K = ⊥ ∨ K = ⊤)
    {k : ℕ} (hk : (xiZ h) ^ k = 1) :
    (xiQuot h S.hA.map_eq S.hCinv) ^ k = 1 := by
  let ξV : ↥C ⧸ A.subgroupOf C ≃* ↥C ⧸ A.subgroupOf C := xiQuot h S.hA.map_eq S.hCinv
  have hξVη : ξV * ξV ^ k = ξV ^ k * ξV := by rw [← pow_succ', ← pow_succ]
  let φ : ↥C ⧸ A.subgroupOf C →* ↥C ⧸ A.subgroupOf C :=
    { toFun := fun x => (ξV ^ k) x * x
      map_one' := by simp
      map_mul' := fun x y => by
        show (ξV ^ k) (x * y) * (x * y) = ((ξV ^ k) x * x) * ((ξV ^ k) y * y)
        rw [map_mul]
        have hc : (ξV ^ k) y * x = x * ((ξV ^ k) y) := quot_comm S.hCd _ _
        calc (ξV ^ k) x * (ξV ^ k) y * (x * y)
            = (ξV ^ k) x * ((ξV ^ k) y * x) * y := by group
          _ = (ξV ^ k) x * (x * ((ξV ^ k) y)) * y := by rw [hc]
          _ = (ξV ^ k) x * x * ((ξV ^ k) y * y) := by group }
  let I : Subgroup (↥C ⧸ A.subgroupOf C) := φ.range
  have hmemφ : ∀ x : ↥C ⧸ A.subgroupOf C, φ x ∈ I :=
    fun x => MonoidHom.mem_range.mpr ⟨x, rfl⟩
  have hIle : I.map ξV.toMonoidHom ≤ I := by
    rintro y ⟨z, hz, rfl⟩
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.mp hz
    show ξV (φ x) ∈ I
    rw [show ξV (φ x) = φ (ξV x) from by
      show ξV ((ξV ^ k) x * x) = (ξV ^ k) (ξV x) * ξV x
      rw [map_mul]
      congr 1
      rw [← MulAut.mul_apply, hξVη, MulAut.mul_apply]]
    exact hmemφ (ξV x)
  have hcard : Nat.card ↥(I.map ξV.toMonoidHom) = Nat.card ↥I :=
    Subgroup.card_map_of_injective (f := ξV.toMonoidHom) (fun a b hab => ξV.injective hab) (K := I)
  have hI : I.map ξV.toMonoidHom = I :=
    Subgroup.eq_of_le_of_card_ge hIle (by rw [hcard])
  rcases hirr I hI with hIbot | hItop
  · apply MulEquiv.ext
    intro x
    have hx : φ x ∈ I := hmemφ x
    rw [hIbot] at hx
    have hx1 : (ξV ^ k) x * x = 1 := Subgroup.mem_bot.mp hx
    have h1 : ((ξV ^ k) x)⁻¹ = x := inv_eq_of_mul_eq_one_right hx1
    have h2 : x⁻¹ = x := inv_eq_of_mul_eq_one_left (quot_sq_one S.hC2 x)
    show (ξV ^ k) x = x
    calc (ξV ^ k) x = (((ξV ^ k) x)⁻¹)⁻¹ := (inv_inv _).symm
      _ = x⁻¹ := by rw [h1]
      _ = x := h2
  · exfalso
    have hβle : ∀ y : ↥C ⧸ A.subgroupOf C, ∀ w : ↥(omega1 P), betaV S y w = 1 := by
      intro y w
      have hy : y ∈ I := by rw [hItop]; exact Subgroup.mem_top y
      obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hy
      rw [← hx]
      show betaV S ((ξV ^ k) x * x) w = 1
      rw [(l8_betaV S).2.1, betaV_xiZ_triv S hk x w]
      rw [← pow_two]
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact h.omega1_sq_eq_one (betaV S x w).2
    obtain ⟨a, b, hab⟩ := (l8_betaV S).2.2.2.2.2
    exact hab (hβle a b)

/-- **The `§4` core applied to `(C/A, Ω₁(P))`.**  Given that `|C/A| = |Ω₁(P)|`, Higman's fourth
auxiliary result in its multiplicative form gives a contradiction. -/
theorem l8_mult_core_apply {h : IsSuzuki2Grp P} {A C : Subgroup P} [hAn : A.Normal]
    (S : D h A C) (hcard : Nat.card (↥C ⧸ A.subgroupOf C) = Nat.card ↥(omega1 P)) : False := by
  obtain ⟨n, hncard⟩ := h.exists_card_omega1_eq_two_pow
  have hn2 : 2 ≤ n := by
    have h4 : 4 ≤ 2 ^ n := by rw [← hncard]; exact h.omega1_card_ge_four
    by_contra hcon
    have h1 : n ≤ 1 := by omega
    have h2 : 2 ^ n ≤ 2 := by
      calc 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) h1
        _ = 2 := by norm_num
    omega
  obtain ⟨hinj, hsurj, hs1, hseq, hpol⟩ := l8_sV S hcard
  let ξV : ↥C ⧸ A.subgroupOf C ≃* ↥C ⧸ A.subgroupOf C := xiQuot h S.hA.map_eq S.hCinv
  let ξW : ↥(omega1 P) ≃* ↥(omega1 P) := xiZ h
  have hseqpow : ∀ (j : ℕ) (x : ↥C ⧸ A.subgroupOf C),
      (ξW ^ j) (sV S x) = sV S ((ξV ^ j) x) := by
    intro j
    induction j with
    | zero => intro x; simp
    | succ j ih =>
        intro x
        calc (ξW ^ (j + 1)) (sV S x) = ξW ((ξW ^ j) (sV S x)) := by
              rw [pow_succ', MulAut.mul_apply]
          _ = ξW (sV S ((ξV ^ j) x)) := by rw [ih]
          _ = sV S (ξV ((ξV ^ j) x)) := hseq _
          _ = sV S ((ξV ^ (j + 1)) x) := by rw [pow_succ', MulAut.mul_apply]
  have hξWtrans : ∀ a b : ↥(omega1 P), a ≠ 1 → b ≠ 1 → ∃ k : ℕ, (ξW ^ k) a = b := by
    intro a b ha hb
    obtain ⟨k, hk⟩ := xi_trans_omega1 h a.2 b.2 (fun hc => ha (Subtype.ext hc))
      (fun hc => hb (Subtype.ext hc))
    exact ⟨k, Subtype.ext (by rw [xiZ_pow_coe]; exact hk)⟩
  have hsne : ∀ a : ↥C ⧸ A.subgroupOf C, a ≠ 1 → sV S a ≠ 1 :=
    fun a ha hc => ha (hinj (by rw [hc, hs1]))
  have hξVtrans : ∀ a b : ↥C ⧸ A.subgroupOf C, a ≠ 1 → b ≠ 1 → ∃ k : ℕ, (ξV ^ k) a = b := by
    intro a b ha hb
    obtain ⟨k, hk⟩ := hξWtrans (sV S a) (sV S b) (hsne a ha) (hsne b hb)
    exact ⟨k, hinj (by rw [← hseqpow k a]; exact hk)⟩
  letI : CommGroup (↥C ⧸ A.subgroupOf C) :=
    { (inferInstance : Group (↥C ⧸ A.subgroupOf C)) with
      mul_comm := fun a b => quot_comm S.hCd a b }
  letI : CommGroup ↥(omega1 P) :=
    { (inferInstance : Group ↥(omega1 P)) with
      mul_comm := fun a b => Subtype.ext (h.omega1_comm a.2 b.2) }
  exact l8_mult_core (n := n)
    (fun v => quot_sq_one S.hC2 v)
    (fun w => by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_one, ← pow_two]
      exact h.omega1_sq_eq_one w.2)
    hn2 (by rw [hcard, hncard]) hncard
    ξV ξW hξVtrans hξWtrans
    (BV S) (l8_BV S).2.1 (l8_BV S).2.2.1 (l8_BV S).2.2.2.1 (l8_BV S).2.2.2.2.1
    (l8_BV S).2.2.2.2.2
    (sV S) hs1 hseq hpol hsne
    (betaV S) (l8_betaV S).2.1 (l8_betaV S).2.2.1 (l8_betaV S).2.2.2.1
    (l8_betaV S).2.2.2.2.1 (l8_betaV S).2.2.2.2.2

/-- The `|C/A| ≤ |Ω₁(P)|` bound: `Ω₁(P)` is a field `𝔽_q` (`q = 2^n`) on which `ξ` acts by
multiplication by a generator, hence `ξ ^ (q-1) = 1` on it (`Work.Higman.omega1_iso_field`); by
Higman's first step (`l8_first_step`) the same holds on the irreducible module `C/A`, and then
`l8_card_le` bounds its cardinality. -/
theorem card_le_apply {h : IsSuzuki2Grp P} {A C : Subgroup P} [hAn : A.Normal]
    (S : D h A C)
    (hirr : ∀ K : Subgroup (↥C ⧸ A.subgroupOf C),
      K.map (xiQuot h S.hA.map_eq S.hCinv).toMonoidHom = K → K = ⊥ ∨ K = ⊤) :
    Nat.card (↥C ⧸ A.subgroupOf C) ≤ Nat.card ↥(omega1 P) := by
  classical
  obtain ⟨n, F, hFfield, hFfin, hFdec, hFchar, mu, hFcard, hn2, hmuord, -, ζ, -, hζmul⟩ :=
    Work.Higman.omega1_iso_field h
  have hWcard : Nat.card ↥(omega1 P) = 2 ^ n := by
    rw [← Nat.card_congr ζ, Nat.card_eq_fintype_card, hFcard]
  have hstep0 : ∀ x : F, (xiZ h) (ζ x) = ζ (mu * x) := by
    intro x
    apply Subtype.ext
    rw [xiZ_apply]
    exact (hζmul x).symm
  have hstep : ∀ (j : ℕ) (x : F), ((xiZ h) ^ j) (ζ x) = ζ (mu ^ j * x) := by
    intro j
    induction j with
    | zero => intro x; simp
    | succ j ih =>
        intro x
        rw [pow_succ', MulAut.mul_apply, ih, hstep0, ← mul_assoc, ← pow_succ']
  have hmu : mu ^ (2 ^ n - 1) = 1 := by
    rw [← hmuord]
    exact orderOf_dvd_iff_pow_eq_one.mp (dvd_refl (orderOf mu))
  have hxiW : (xiZ h) ^ (2 ^ n - 1) = 1 := by
    apply MulEquiv.ext
    intro w
    obtain ⟨x, rfl⟩ := ζ.surjective w
    rw [hstep (2 ^ n - 1) x, hmu, one_mul]
    rfl
  have hξV : (xiQuot h S.hA.map_eq S.hCinv) ^ (2 ^ n - 1) = 1 :=
    l8_first_step S hirr hxiW
  letI : CommGroup (↥C ⧸ A.subgroupOf C) :=
    { (inferInstance : Group (↥C ⧸ A.subgroupOf C)) with
      mul_comm := fun a b => quot_comm S.hCd a b }
  have hle := l8_card_le (V := ↥C ⧸ A.subgroupOf C)
    (fun v => quot_sq_one S.hC2 v) (xiQuot h S.hA.map_eq S.hCinv) (by omega : 1 ≤ n) hξV hirr
  rwa [hWcard]

/-- **Higman 1963, auxiliary result 8** (own copy for the Lemma-9 development).  The file
`Submission/Work/Higman/higman_lemma8.lean` states the same result and is the *only* remaining
`sorry` in the dependency cone of `Work.Higman.maximal_abelian_invariant_ge_phi`
(`Submission/Work/Higman/maximal_abelian_invariant_ge_phi.lean`); switch that import to this file
once it is proved.

`A` is a normal abelian `ξ`-subgroup of a Suzuki 2-group `P`, `C ⊵ A` is normal, `ξ`-invariant,
`A < C`, `C/A` is a minimal normal `ξ`-section (`hcover`), `C² ≤ A` and `C' = ⁅C,C⁆ = A`.  Then
`A` has exponent dividing `2`: `∀ a ∈ A, a * a = 1`.

Note `Φ(C) = C²·C' = A` (`hC2` and `hCd`), so `C/A` is elementary abelian and irreducible.

HIGMAN'S ARGUMENT (pp. 86–87); the structure is worked out in
`Submission/Work/Higman/MSA_NOTES.md` §6.  Write `γᵢ` for the lower central series of `C`.  Then
`γ₂ = C' = A`, `γ₃ = [A,C] = A²` (unless `A² = 1`, which is exactly the goal), `γ₄ = [A²,C] =
([A,C])² = A⁴`, and generally `γᵢ = A^(2^(i-1))`.  Hence `L₂ = γ₂/(γ₂²γ₃) = A/A²` and
`L₃ = γ₃/(γ₃²γ₄) = A²/A⁴` are isomorphic as `ξ`-modules under the power map `A/A² → A²/A⁴`,
`x ↦ x²` (using `homogeneous_structure`: `A` is homocyclic of exponent `2^e`, `|A^(2^i)| =
q^(e-i)` with `q = |A ⊓ Ω₁| = |Ω₁|`).  Higman's §4 fourth auxiliary result (in the setting
`H² = H₂` of that section, `L₃` is not `ξ`-isomorphic to `L₂`) then gives a contradiction unless
`A² = 1`.

Inputs for the §4 comparison: `C/A` is irreducible (`hcover`); `ξ` acts transitively on
`(A/A²) ∖ 1` (`Work.Higman.xi_trans_quot_sq`); `|A/A²| = |Ω₁| ≥ 4`
(`Work.Higman.IsSuzuki2Grp.omega1_card_ge_four`); the squaring map `s : C/A → A/A²`,
`uA ↦ u²A²`, is well defined and `ξ`-equivariant with polarization the commutator pairing
`B : (C/A) × (C/A) → A/A²`, `B(u,v) = ⁅u,v⁆` (alternating, biadditive, `ξ`-equivariant, non-zero
because `[C,C] = A ⊄ A²`); the bracket `⌊·,·⌋ : (C/A) × (A/A²) → A²/A⁴` is `ξ`-equivariant and
onto (it comes from `[C,A] = A²`).  For the eigenvalue bookkeeping, `C/A`, `A/A²` and `A²/A⁴` are
irreducible `𝔽₂⟨ξ⟩`-modules of order `2^n`, identified with `𝔽_{2^n}`: the eigenvalues of `ξ` on
`A/A²` are `λ^(2^i)` with `λ` of order `2^n - 1`, while those on `Λ²(C/A)` are `μ^(2^i + 2^j)`
with `i ≠ j`; `Work.Higman.equivariant_bihom_trivial` is the formalised Gorenstein–Thompson
fourth auxiliary result in elementary abelian form.  The arithmetic input
`Work.Higman.pow_two_mod_unique` (already proved) controls when `2^p + t·2^q ≡ t [MOD 2^n - 1]`.

Other files attacking this result (read them, some of their lemmas are already proved):
`Submission/Work/Higman/higman_lemma8.lean` (with a detailed plan in its docstring),
`Submission/Work/Higman/higman_lemma8_plan.md`, `Submission/Work/Higman/omega1_iso_field.lean`,
`Submission/Work/Higman/L1_iso_field.lean`, `Submission/Work/Higman/c4_field_core.lean`. -/
theorem higman_lemma8_msa {P : Type} [Group P] [Finite P]
    (h : Work.Higman.IsSuzuki2Grp P) {A C : Subgroup P}
    (hA : Work.Higman.IsXiAbelNormal h A)
    (hCn : C.Normal) (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C)
    (hAC : A ≤ C) (hCA : A ≠ C)
    (hcover : ∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
      A ≤ D → D ≤ C → D = A ∨ D = C)
    (hC2 : Work.Higman.powSub C 2 ≤ A)
    (hCd : ⁅C, C⁆ = A) :
    ∀ a ∈ A, a * a = 1 := by
  intro a ha
  by_cases hA2 : Work.Higman.powSub A 2 = ⊥
  · -- then every element of `A` is an involution
    have hmem : a * a ∈ Work.Higman.powSub A 2 := by
      rw [← pow_two]; exact pow_mem_powSub (A := A) ha
    rw [hA2] at hmem
    simpa using hmem
  · -- the hard case `A ≠ ⊥`, `A ^ (2) ≠ ⊥`
    have hAne : A ≠ ⊥ := by
      intro hbot
      exact hA2 (by rw [hbot]; exact le_antisymm (powSub_le (by norm_num)) bot_le)
    have hOmega : Work.Higman.omega1 P ≤ A :=
      Work.Higman.sq_omega1_le_of_isXiAbelNormal_ne_bot h hA hAne
    obtain ⟨e, he2, he1, htopA, hkey⟩ := Work.Higman.MSA.l8_setup h hA hAne hA2 hOmega
    haveI : A.Normal := hA.normal
    let S : L8.D h A C :=
      { hA := hA, hCn := hCn, hCinv := hCinv, hAC := hAC, hCA := hCA, hcover := hcover,
        hC2 := hC2, hCd := hCd, hAne := hAne, hOmega := hOmega, e := e,
        he := (by omega), he2 := he2, he1 := he1, htopA := htopA, hkey := hkey }
    -- `C/A` is an irreducible `ξ`-module
    have hirr : ∀ K : Subgroup (↥C ⧸ A.subgroupOf C),
        K.map (L8.xiQuot h S.hA.map_eq S.hCinv).toMonoidHom = K → K = ⊥ ∨ K = ⊤ :=
      fun K hK => l8_quot_irred S (K := K) hK
    -- `sV : C/A → Ω₁(P)` is surjective
    have hsurj : Function.Surjective (L8.sV S) := (l8_sV_aux S).2.2.2
    have hge : Nat.card ↥(Work.Higman.omega1 P) ≤ Nat.card (↥C ⧸ A.subgroupOf C) :=
      Nat.card_le_card_of_surjective (L8.sV S) hsurj
    -- hence `|C/A| = |Ω₁(P)|` and Higman's §4 core gives a contradiction
    exact (l8_mult_core_apply S (le_antisymm (card_le_apply S hirr) hge)).elim

end Work.Higman.MSA
