import Mathlib
import Submission.Work.ZASS.Leaf9
import Submission.Work.ZASS.Z5
import Submission.Work.ZASS.card_G
import Submission.Work.ZASS.psl_smul_ptOf
import Submission.Work.ZASS.bruhat_decomposition
import Submission.Work.ZASS.zassInvolutionSwapProp
import Submission.Work.ZASS2.zassCoord
import Submission.Work.ZASS2.EndgameCore
import Submission.Work.PSL2.Basic
import Submission.Work.PSL2.Card

namespace Work.ZASS2

open scoped MatrixGroups LinearAlgebra.Projectivization
open Matrix

open Work.GW2
open Work.Zassenhaus (borel pairStab)

/-! ## Elementary auxiliary facts -/

/-- The Weyl element `[[0,1],[-1,0]] ∈ PSL(2,F)` sends `∞ = [1:0]` to `0 = [0:1]` and `0`
back to `∞` (the two "endpoints" of the affine chart, where `psl_smul_ptOf_weyl` does not
apply because its hypothesis `t ≠ 0` fails). -/
theorem pslWeyl_smul_ptInf_ptZero (F : Type) [Field F] :
    Work.PSL2.pslWeyl F • Work.PSL2.ptInf F = Work.PSL2.ptZero F ∧
      Work.PSL2.pslWeyl F • Work.PSL2.ptZero F = Work.PSL2.ptInf F := by
  have h1 : SpecialLinearGroup.toLin' (Work.PSL2.weyl F) ![1, 0] =
      (-1 : F) • ![0, 1] := by
    rw [SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply, Work.PSL2.coe_weyl]
    ext i
    fin_cases i <;> simp [Matrix.mulVec]
  have h2 : SpecialLinearGroup.toLin' (Work.PSL2.weyl F) ![0, 1] = ![1, 0] := by
    rw [SpecialLinearGroup.toLin'_apply, Matrix.toLin'_apply, Work.PSL2.coe_weyl]
    ext i
    fin_cases i <;> simp [Matrix.mulVec]
  constructor
  · change ((Work.PSL2.weyl F : SpecialLinearGroup (Fin 2) F) :
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) • Work.PSL2.ptInf F = Work.PSL2.ptZero F
    simp only [Work.PSL2.ptInf, Work.PSL2.ptZero, Work.PSL2.ptOf]
    rw [Matrix.ProjectiveSpecialLinearGroup.smul_proj_mk,
      Projectivization.matrixSpecialLinearGroup_smul_def, Projectivization.smul_mk]
    change Projectivization.mk F (SpecialLinearGroup.toLin' (Work.PSL2.weyl F) ![1, 0]) _ =
      Projectivization.mk F ![0, 1] _
    exact (Projectivization.mk_eq_mk_iff F _ _ _ _).mpr ⟨(-1 : Fˣ), by simpa using h1.symm⟩
  · change ((Work.PSL2.weyl F : SpecialLinearGroup (Fin 2) F) :
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) • Work.PSL2.ptZero F = Work.PSL2.ptInf F
    simp only [Work.PSL2.ptInf, Work.PSL2.ptZero, Work.PSL2.ptOf]
    rw [Matrix.ProjectiveSpecialLinearGroup.smul_proj_mk,
      Projectivization.matrixSpecialLinearGroup_smul_def, Projectivization.smul_mk]
    change Projectivization.mk F (SpecialLinearGroup.toLin' (Work.PSL2.weyl F) ![0, 1]) _ =
      Projectivization.mk F ![1, 0] _
    exact (Projectivization.mk_eq_mk_iff F _ _ _ _).mpr ⟨1, by rw [one_smul, h2]⟩

/-- A finite field of cardinality `p ^ k` with `k ≠ 0` is `GaloisField p k`. -/
theorem existsRingEquivGaloisField {p k : ℕ} [Fact p.Prime] {F : Type} [Field F] [Fintype F]
    (hk : k ≠ 0) (h : Fintype.card F = p ^ k) : Nonempty (F ≃+* GaloisField p k) := by
  haveI : Fintype (GaloisField p k) := Fintype.ofFinite _
  have hcard : Fintype.card (GaloisField p k) = p ^ k := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card p k hk]
  exact ⟨FiniteField.ringEquivOfCardEq (h.trans hcard.symm)⟩

/-- Every scaling factor `α h` of the coordinates is a nonzero element of the field. -/
theorem alphaNeZero {G X : Type} [Group G] [MulAction G X] {inf zero : X} {U : Subgroup G}
    (C : ZassCoords G X inf zero U) (h : pairStab G inf zero) : C.α h ≠ 0 := by
  intro h0
  obtain ⟨x, hx⟩ : ∃ x, C.Θ x = some (1 : C.E) := (C.Θ).surjective (some 1)
  have hfix : (h : G) • zero = zero := (Work.Zassenhaus.mem_pairStab_iff.mp h.2).1
  have hx1 : (h : G) • x = zero := by
    have hstep := C.scale h x
    rw [hx, h0] at hstep
    simp only [Option.map_some, zero_mul] at hstep
    exact C.Θ.injective (hstep.trans C.Θ_zero.symm)
  have hxz : x = zero := by
    have h2 : (h : G) • x = (h : G) • zero := by rw [hx1, hfix]
    simpa using congrArg (fun y => (h : G)⁻¹ • y) h2
  rw [hxz, C.Θ_zero] at hx
  exact one_ne_zero (Option.some.inj hx).symm

/-- The coefficient field of coordinates has `p ^ k` elements. -/
theorem cardE {G X : Type} [Group G] [MulAction G X] {inf zero : X} {U : Subgroup G}
    (C : ZassCoords G X inf zero U) {p k : ℕ} (hcardX : Nat.card X = p ^ k + 1) :
    Fintype.card C.E = p ^ k := by
  have h1 : Nat.card (Option C.E) = Fintype.card C.E + 1 := by
    rw [Nat.card_eq_fintype_card (α := Option C.E), Fintype.card_option]
  have h2 : Nat.card (Option C.E) = Nat.card X := (Nat.card_congr C.Θ).symm
  have : Fintype.card C.E + 1 = p ^ k + 1 := by rw [← h1, h2, hcardX]
  omega

/-! ## The three generating cases -/

/-- `u ∈ U` acts on `ℙ¹` through `pslUnipotent (τ u)`. -/
theorem phi_eq_pslUnipotent {G X : Type} [Group G] [MulAction G X] {inf zero : X}
    {U : Subgroup G} (C : ZassCoords G X inf zero U) (u : U) :
    ∀ x : X, coordsEquiv C ((u : G) • x) =
      Work.PSL2.pslUnipotent C.E (C.τ u) • coordsEquiv C x := by
  intro x
  show ptEquiv C.E (C.Θ ((u : G) • x)) =
    Work.PSL2.pslUnipotent C.E (C.τ u) • ptEquiv C.E (C.Θ x)
  rw [C.trans u x]
  exact ptEquiv_map_add C.E (C.τ u) (C.Θ x)

/-- `h ∈ G_{∞0}` acts on `ℙ¹` through `pslDiag a` for a unit `a` with `a² = α h`. -/
theorem phi_eq_pslDiag {G X : Type} [Group G] [MulAction G X] {inf zero : X}
    {U : Subgroup G} (C : ZassCoords G X inf zero U) (h : pairStab G inf zero)
    (hh : C.α h ≠ 0) :
    ∃ a : C.Eˣ, (a : C.E) ^ 2 = C.α h ∧ ∀ x : X,
      coordsEquiv C ((h : G) • x) = Work.PSL2.pslDiag C.E a • coordsEquiv C x := by
  obtain ⟨d, hd⟩ := (C.α_range (C.α h) hh).mp ⟨h, rfl⟩
  have hd0 : d ≠ 0 := fun h0 => hh (by rw [hd, h0, mul_zero])
  refine ⟨Units.mk0 d hd0, ?_, fun x => ?_⟩
  · rw [Units.val_mk0, sq, ← hd]
  · show ptEquiv C.E (C.Θ ((h : G) • x)) =
      Work.PSL2.pslDiag C.E (Units.mk0 d hd0) • ptEquiv C.E (C.Θ x)
    rw [C.scale h x, ← ptEquiv_map_mul C.E (Units.mk0 d hd0) (C.Θ x)]
    rw [show (fun t : C.E => ((Units.mk0 d hd0 : C.Eˣ) : C.E) ^ 2 * t) =
        (fun t : C.E => C.α h * t) from
      funext (fun t => by rw [Units.val_mk0, sq, ← hd])]

/-- `s` acts on `ℙ¹` through `pslDiag β * pslWeyl` where `-c = β²`. -/
theorem phi_eq_pslDiagWeyl {G X : Type} [Group G] [MulAction G X] {inf zero : X}
    {U : Subgroup G} (C : ZassCoords G X inf zero U) (s : G) {c : C.E}
    (hform : ∀ (x : X) (y : C.E), y ≠ 0 → C.Θ x = some y → C.Θ (s • x) = some (c / y))
    (hsinf : s • inf = zero) (hszero : s • zero = inf) {β : C.Eˣ}
    (hβ : (β : C.E) ^ 2 = -c) :
    ∀ x : X, coordsEquiv C (s • x) =
      (Work.PSL2.pslDiag C.E β * Work.PSL2.pslWeyl C.E) • coordsEquiv C x := by
  intro x
  have hw := pslWeyl_smul_ptInf_ptZero C.E
  cases hx : C.Θ x with
  | none =>
      have hxinf : x = inf := C.Θ.injective (by rw [hx, C.Θ_inf])
      rw [hxinf, hsinf, coordsEquiv_zero, coordsEquiv_inf, mul_smul, hw.1,
        ← Work.PSL2.ptOf_zero, Work.ZASS.psl_smul_ptOf_diag, mul_zero]
  | some y =>
      by_cases hy : y = 0
      · subst hy
        have hxzero : x = zero := C.Θ.injective (by rw [hx, C.Θ_zero])
        rw [hxzero, hszero, coordsEquiv_inf, coordsEquiv_zero, mul_smul, hw.2,
          Work.ZASS.pslDiag_smul_ptInf]
      · rw [coordsEquiv_apply, coordsEquiv_apply, hform x y hy hx, hx, ptEquiv_some,
          ptEquiv_some, mul_smul, Work.ZASS.psl_smul_ptOf_weyl C.E hy,
          Work.ZASS.psl_smul_ptOf_diag]
        exact congrArg (Work.PSL2.ptOf C.E) (by rw [hβ, neg_mul_neg, div_eq_mul_inv])

/-! ## Membership of `φ g` in the image of `PSL(2,C.E)` -/

/-- If `p ∈ PSL(2,C.E)` acts on `X` exactly as `g`, then `phiPerm C g` is in the range. -/
theorem mem_pslRange_of_forall {G X : Type} [Group G] [MulAction G X] {inf zero : X}
    {U : Subgroup G} (C : ZassCoords G X inf zero U) {g : G} {p : PSL(2, C.E)}
    (h : ∀ x : X, coordsEquiv C (g • x) = p • coordsEquiv C x) :
    phiPerm C g ∈ pslRange C :=
  ⟨p, (phiPerm_eq_pslPermHom C h).symm⟩

/-- **Z6.6, membership.**  The permutation of `ℙ¹` induced by any `g ∈ G` lies in the image
of `PSL(2, C.E)`: `G` is generated by `U`, `G_{∞0}` and `s`, and the images of those three
are the images of `pslUnipotent`, `pslDiag` and `pslDiag β * pslWeyl`. -/
theorem phiPerm_mem_pslRange {G X : Type} [Group G] [Finite G] [MulAction G X] [Finite X]
    {p k : ℕ} [Fact p.Prime] (hp : Odd p) (hZ : ZassHyps2 G X (p ^ k)) {inf zero : X}
    (hne : inf ≠ zero) {U : Subgroup G} (hU : ZassUData G X p k inf zero U)
    (C : ZassCoords G X inf zero U) {s : G} (hsinf : s • inf = zero)
    (hszero : s • zero = inf) {c : C.E} (hc0 : c ≠ 0) (hcsq : IsSquare (-c))
    (hform : ∀ (x : X) (y : C.E), y ≠ 0 → C.Θ x = some y → C.Θ (s • x) = some (c / y)) :
    ∀ g : G, phiPerm C g ∈ pslRange C := by
  haveI : FaithfulSMul G X := hZ.1
  have hss : s * s = 1 := mul_self_eq_one_of_swapOpt C s hc0 hform hsinf hszero
  obtain ⟨-, hbru⟩ :=
    Work.ZASS.bruhat_decomposition hp hZ hne hU.1 hU.2.1 hU.2.2.1 hss hsinf hszero
  have hdec : U ⊔ pairStab G inf zero = borel G inf := hU.2.2.2.1.1
  have hgen := closure_union_pairStab_singleton_eq_top hdec hbru
  have hle : Subgroup.closure ((U : Set G) ∪ (pairStab G inf zero : Set G) ∪ {s}) ≤
      (pslRange C).comap (phiHom C) := by
    rw [Subgroup.closure_le]
    rintro g ((hgU | hgH) | hgs)
    · exact mem_pslRange_of_forall C (phi_eq_pslUnipotent C ⟨g, hgU⟩)
    · obtain ⟨a, -, hforall⟩ :=
        phi_eq_pslDiag C ⟨g, hgH⟩ (alphaNeZero C ⟨g, hgH⟩)
      exact mem_pslRange_of_forall C hforall
    · rw [Set.mem_singleton_iff] at hgs
      rw [hgs]
      obtain ⟨r, hr⟩ := hcsq
      have hr0 : r ≠ 0 := fun h0 => hc0 (neg_eq_zero.mp (by rw [hr, h0, mul_zero]))
      have hβ : ((Units.mk0 r hr0 : C.Eˣ) : C.E) ^ 2 = -c := by
        rw [Units.val_mk0, sq, ← hr]
      exact mem_pslRange_of_forall C (phi_eq_pslDiagWeyl C s hform hsinf hszero hβ)
  intro g
  refine hle ?_
  rw [hgen]
  trivial

/-! ## Assembly: the monoid homomorphism `Ψ` -/

/-- **Z6.6.**  With the coordinates `C` and an `s` acting as `y ↦ c/y`, the action of `G` on
`X` is equivalent to the standard action of `PSL(2,C.E)` on `ℙ¹(C.E)`. -/
theorem endgameAux {G X : Type} [Group G] [Finite G] [MulAction G X] [Finite X] {p k : ℕ}
    [Fact p.Prime] (hp : Odd p) (hZ : ZassHyps2 G X (p ^ k)) {inf zero : X} (hne : inf ≠ zero)
    {U : Subgroup G} (hU : ZassUData G X p k inf zero U) (C : ZassCoords G X inf zero U)
    {s : G} (hsinf : s • inf = zero) (hszero : s • zero = inf) {c : C.E} (hc0 : c ≠ 0)
    (hcsq : IsSquare (-c))
    (hform : ∀ (x : X) (y : C.E), y ≠ 0 → C.Θ x = some y → C.Θ (s • x) = some (c / y)) :
    ∃ (Φ : X ≃ ℙ C.E (Fin 2 → C.E)) (Ψ : G →* PSL(2, C.E)),
      ∀ (g : G) (x : X), Φ (g • x) = Ψ g • Φ x := by
  have hmem : ∀ g : G, phiPerm C g ∈ pslRange C :=
    phiPerm_mem_pslRange hp hZ hne hU C hsinf hszero hc0 hcsq hform
  let iso : PSL(2, C.E) ≃* pslRange C :=
    MulEquiv.ofBijective (pslPermHom C).rangeRestrict
      ⟨fun a b h => pslPermHom_injective C (congrArg Subtype.val h),
        (pslPermHom C).rangeRestrict_surjective⟩
  let fL : G →* pslRange C :=
    { toFun := fun g => ⟨phiPerm C g, hmem g⟩
      map_one' := Subtype.ext (phiPerm_one C)
      map_mul' := fun g g' => Subtype.ext (phiPerm_mul C g g') }
  refine ⟨coordsEquiv C, (iso.symm : pslRange C →* PSL(2, C.E)).comp fL, fun g x => ?_⟩
  have hkey : pslPermHom C (iso.symm (fL g)) = phiPerm C g :=
    congrArg Subtype.val (MulEquiv.apply_symm_apply iso (fL g))
  rw [← phiPerm_coordsEquiv C g x, ← hkey]
  rfl

/-! # ZASS2 leaf Z6.6: the endgame (`Work.GW2.ZassEndgameProp`)

Statement (fixed in `Submission/Work/ZASS/Leaf9.lean`): given the coordinates
`C : ZassCoords G X inf zero U`, an `s` interchanging `inf` and `zero` acting as `y ↦ c/y`
(with `-c` a square) on the affine chart, there are `Φ : X ≃ ℙ¹(GaloisField p k)` and
`Ψ : G →* PSL(2, GaloisField p k)` with `Φ (g • x) = Ψ g • Φ x`.

Route.  `Submission/Work/ZASS2/zassCoord.lean` provides the affine chart
`Work.ZASS2.ptEquiv : Option E ≃ ℙ¹(E)` (with `ptEquiv_none`, `ptEquiv_some`,
`ptEquiv_map_add`, `ptEquiv_map_mul`) — import it.

* `Nat.card C.E = p^k`: from `C.Θ : X ≃ Option C.E` and `Nat.card X = p^k + 1`; then
  `C.E ≃+* GaloisField p k` by `FiniteField.ringEquivOfCardEq` (`cardE`,
  `existsRingEquivGaloisField`), and the coordinates are transported by `transportCoords`.
* Set `Θ : X ≃ Option (GaloisField p k)` accordingly, and `Φ := Θ.trans (ptEquiv _)`
  (`coordsEquiv`).
* `G = ⟨G_∞, s⟩`: from the hypothesis on the action of `s`, `s * s = 1` follows (the induced
  permutation of `Option C.E` is an involution, and the action is faithful)
  (`mul_self_eq_one_of_swapOpt`), so `Work.ZASS.bruhat_decomposition` applies and
  `Subgroup.closure ({borel G inf} ∪ {s}) = ⊤` (`closure_union_pairStab_singleton_eq_top`).
* The permutation `φ g := Φ ∘ (g • ·) ∘ Φ⁻¹` of `ℙ¹` lies in the image `L` of the action of
  `PSL(2, K)` on `ℙ¹(K)` for `g` in a generating set: for `u ∈ U` it is
  `Work.PSL2.pslUnipotent (τ u)` (`phi_eq_pslUnipotent`); for `h ∈ H` it is
  `Work.PSL2.pslDiag a` where `a² = C.α h` (`phi_eq_pslDiag`, using `C.scale`, `C.α_range`
  — the image of `α` is the nonzero squares — and `alphaNeZero`); for `s` it is
  `Work.PSL2.pslDiag β * Work.PSL2.pslWeyl` where `-c = β²` (`phi_eq_pslDiagWeyl`, using
  `Work.ZASS.psl_smul_ptOf_weyl`, `Work.ZASS.psl_smul_ptOf_diag` and
  `pslWeyl_smul_ptInf_ptZero`).
* Hence `φ` factors through the image: the action of `PSL(2,K)` on `ℙ¹(K)` is faithful
  (`pslPermHom_injective`), so `MulAction.toPermHom` restricts to an isomorphism
  `PSL(2,K) ≃* L` and `Ψ g` is the preimage of `φ g`; `Ψ` is a monoid homomorphism by
  faithfulness, and `Φ (g • x) = Ψ g • Φ x` holds by construction (`endgameAux`). -/
theorem zassEndgame : Work.GW2.ZassEndgameProp := by
  intro G X _ _ _ _ p k _ hp hq hZ inf zero hne U hU C s hsinf hszero c hc0 hcsq hform
  have hcardX : Nat.card X = p ^ k + 1 := hZ.2.1
  have hcardE : Fintype.card C.E = p ^ k := cardE C hcardX
  have hk : k ≠ 0 := by rintro rfl; simp at hq
  haveI : Fintype (GaloisField p k) := Fintype.ofFinite _
  obtain ⟨e⟩ := existsRingEquivGaloisField (p := p) (k := k) hk hcardE
  have hc0' : e c ≠ 0 := fun h0 => hc0 ((RingEquiv.map_eq_zero_iff e).mp h0)
  have hcsq' : IsSquare (-(e c)) := by
    obtain ⟨r, hr⟩ := hcsq
    exact ⟨e r, by rw [← map_neg, hr, map_mul]⟩
  have hform' : ∀ (x : X) (y : GaloisField p k), y ≠ 0 →
      (transportCoords C e).Θ x = some y →
      (transportCoords C e).Θ (s • x) = some (e c / y) := by
    intro x y hy hxy
    have h1 : Option.map e (C.Θ x) = some y := by
      rw [← transportCoords_Θ]; exact hxy
    obtain ⟨z, hz, hzy⟩ := Option.map_eq_some_iff.mp h1
    subst hzy
    have hz0 : z ≠ 0 := fun h0 => hy (by rw [h0, map_zero])
    have hstep : C.Θ (s • x) = some (c / z) := hform x z hz0 hz
    rw [transportCoords_Θ, hstep, Option.map_some]
    simp only [div_eq_mul_inv, map_mul, map_inv₀]
  obtain ⟨Φ, Ψ, hΦ⟩ :=
    endgameAux (G := G) (X := X) hp hZ hne hU (transportCoords C e) hsinf hszero hc0' hcsq'
      hform'
  exact ⟨Φ, Ψ, hΦ⟩

end Work.ZASS2
