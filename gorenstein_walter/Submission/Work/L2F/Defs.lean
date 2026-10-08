/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# AREA L2F : the `PSL(2,q)` / `PGL(2,q)` model facts for the Gorenstein–Walter theorem

This file is the *interface* of the area `Submission/Work/L2F/` (namespace `Work.L2F`).
Everything else in the area is stated against the definitions below.

## The four area deliverables (Props)

Copied verbatim from `Submission/Work/_design_gw/Contracts2.lean` (there they live in
namespace `GW2`; here they are reproved in namespace `Work.L2F`, and `Bridge.lean` transfers
the proofs back to the `GW2` names):

* `L2SylowDihedralProp`         — Sylow 2-subgroups of `L₂(q)`, `q` odd `≥ 5`, are dihedral;
* `L2InvolutionCentralizerProp` — the centralizer of an involution is dihedral of order `q ∓ 1`;
* `L2FourGroupProp`             — four-groups are self-centralizing in `L₂(q)` and `PGL₂(q)`;
* `L2TIProp`                    — the two tori and the unipotent subgroup, with the TI property,
  the normalizer orders and the dihedral normalizers.

## Model vocabulary

Everything is built on the concrete model `PSL(2,F) = SL(2,F)/Z(SL(2,F))` of Mathlib (see
`Submission/Work/PSL2/Basic.lean` for `diag`, `unipotent`, `weyl`, `pslMap`, …).

* `z F`        : the element `[[0,1],[-1,0]]` of `SL(2,F)`, with `z * z = -1` (as `z² = -1`);
* `pslZ F`     : its image in `PSL(2,F)`, the base involution;
* `negOne F`   : the matrix `-1` of `SL(2,F)` (the nontrivial central element);
* `circle F`   : `C_{SL(2,F)}(z) = {[[a,b],[-b,a]] | a² + b² = 1}`, cyclic of order `q ∓ 1`;
* `normZ F`    : the normalizer of `⟨z⟩` in `SL(2,F)`, namely `circle ∪ {x | x z x⁻¹ = -z}`;
* `hypTorus F d` : the norm-one subgroup `{[[a, d*b],[b,a]] | a² - d b² = 1}` of `SL(2,F)`,
  cyclic of order `q + 1` when `d` is a nonsquare (the "non-split torus");
* `torus F`    : the diagonal torus `{diag(a,a⁻¹)}`, cyclic of order `q - 1` (split torus);
* `borel F`    : the upper triangular subgroup of `SL(2,F)`;
* `quadAlg F d`, `quadNormSubgroup F d` : the quadratic algebra `F[X]/(X²-d)` (a field for `d` a
  nonsquare) and the norm-one subgroup of its units, used to see `hypTorus F d` is cyclic.

Images in `PSL(2,F)` are named `psl` + the name: `pslUnipotent`, `pslSplitTorus`,
`pslHypTorus`, `pslBorel`, `pslZ`.
-/
import Mathlib
import Submission.Work.PSL2.Basic
import Submission.Work.PSL2.Card

open scoped MatrixGroups
open Matrix
open Subgroup (centralizer normalizer zpowers)

namespace Work.L2F

/-! ## Klein four-groups -/

/-- `V ≤ G` is a Klein four-group. -/
def IsFourGroup {G : Type*} [Group G] (V : Subgroup G) : Prop :=
  Nat.card V = 4 ∧ ∀ v ∈ V, v ^ 2 = 1

/-! ## The model

All definitions take `F` first (as a `variable`).  They involve no proofs, so that statements
about them can be written down immediately; the basic API is proved in the other files of the
area. -/

section Model

variable (F : Type*) [Field F]

/-- The matrix `[[0,1],[-1,0]]` of `SL(2,F)`; its square is `-1`. -/
def z : SL(2, F) := Work.PSL2.weyl F

/-- The image of `z` in `PSL(2,F)` : the base involution. -/
def pslZ : PSL(2, F) := Work.PSL2.pslWeyl F

/-- The element `-1` of `SL(2,F)` (the matrix `-1`), i.e. the nontrivial central element. -/
def negOne : SL(2, F) :=
  ⟨-1, by rw [Matrix.det_neg, Matrix.det_one, Fintype.card_fin]; norm_num⟩

/-- `C_{SL(2,F)}(z)`, to be described as `{aI + b z | a² + b² = 1}`. -/
def circle : Subgroup (SL(2, F)) := Subgroup.centralizer ({z F} : Set (SL(2, F)))

/-- The normalizer of `⟨z⟩` in `SL(2,F)`. -/
def normZ : Subgroup (SL(2, F)) := Subgroup.normalizer (Subgroup.zpowers (z F))

/-- The set of matrices `[[a, d*b],[b,a]]` with `a² - d b² = 1`, inside `SL(2,F)`.  It is a
subgroup; we define `hypTorus` as its closure so that no proof is needed here, and prove the
membership description in `Conic.lean`. -/
def hypTorusSet (d : F) : Set (SL(2, F)) :=
  {x | ∃ a b : F, a ^ 2 - d * b ^ 2 = 1 ∧
      ((x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) = !![a, d * b; b, a]}

/-- The "non-split torus" of `SL(2,F)` attached to `d`, as the closure of `hypTorusSet`. -/
def hypTorus (d : F) : Subgroup (SL(2, F)) := Subgroup.closure (hypTorusSet F d)

/-- The diagonal (split) torus of `SL(2,F)` : `{diag(a,a⁻¹)}`. -/
def torus : Subgroup (SL(2, F)) := (Work.PSL2.diagHom F).range

/-- The upper unipotent subgroup of `SL(2,F)`. -/
def unipotentSubgroup : Subgroup (SL(2, F)) := Work.PSL2.unipotentSubgroup F

/-- The set of upper triangular matrices, as a set. -/
def borelSet : Set (SL(2, F)) := {x | ((x : SL(2, F)) : Matrix (Fin 2) (Fin 2) F) 1 0 = 0}

/-- The Borel subgroup (upper triangular matrices) of `SL(2,F)`. -/
def borel : Subgroup (SL(2, F)) := Subgroup.closure (borelSet F)

/-- The image of the unipotent subgroup in `PSL(2,F)` (order `q` in the finite case). -/
def pslUnipotent : Subgroup (PSL(2, F)) := (unipotentSubgroup F).map (Work.PSL2.pslMap F)

/-- The image of the split torus in `PSL(2,F)` (order `(q-1)/2`). -/
def pslSplitTorus : Subgroup (PSL(2, F)) := (torus F).map (Work.PSL2.pslMap F)

/-- The image of the non-split torus in `PSL(2,F)` (order `(q+1)/2` for `d` a nonsquare). -/
def pslHypTorus (d : F) : Subgroup (PSL(2, F)) := (hypTorus F d).map (Work.PSL2.pslMap F)

/-- The image of the Borel subgroup in `PSL(2,F)` (the normalizer of `pslUnipotent`). -/
def pslBorel : Subgroup (PSL(2, F)) := (borel F).map (Work.PSL2.pslMap F)

end Model

/-! ## The quadratic algebra `F[X]/(X² - d)`

Used to prove that `hypTorus F d` is cyclic: for `d` a nonsquare this is a field, its units are
cyclic, and `hypTorus F d` is isomorphic to the norm-one subgroup of its units. -/

section QuadAlg

variable (F : Type*) [Field F]

/-- The quadratic algebra `F[X]/(X²-d)`. -/
abbrev quadAlg (d : F) : Type _ := AdjoinRoot (Polynomial.X ^ 2 - Polynomial.C d : Polynomial F)

/-- The "conjugation" `a + bX ↦ a - bX` of the quadratic algebra, as a ring homomorphism. -/
noncomputable def quadConj (d : F) : quadAlg F d →+* quadAlg F d :=
  AdjoinRoot.lift (AdjoinRoot.of _) (-AdjoinRoot.root _) (by
    have h := AdjoinRoot.eval₂_root
      (Polynomial.X ^ 2 - Polynomial.C d : Polynomial F)
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_pow, Polynomial.eval₂_X,
      Polynomial.eval₂_C] at h ⊢
    rw [show (-AdjoinRoot.root (Polynomial.X ^ 2 - Polynomial.C d : Polynomial F)) ^ 2 =
      (AdjoinRoot.root (Polynomial.X ^ 2 - Polynomial.C d : Polynomial F)) ^ 2 from by ring]
    exact h)

end QuadAlg

/-! ## The Prop statements of the area (verbatim from `Contracts2.lean`) -/

/-- Sylow 2-subgroups of `L₂(q)`, `q` odd `≥ 5`, are dihedral. -/
def L2SylowDihedralProp : Prop :=
  ∀ (p k : ℕ) [Fact p.Prime], Odd p → 5 ≤ p ^ k →
    ∀ S : Sylow 2 (PSL(2, GaloisField p k)), ∃ n : ℕ, 2 ≤ n ∧
      Nonempty ((S : Subgroup (PSL(2, GaloisField p k))) ≃* DihedralGroup n)

/-- The centralizer of an involution of `L₂(q)` (`q` odd, `≥ 5`) is dihedral of order `q ∓ 1`. -/
def L2InvolutionCentralizerProp : Prop :=
  ∀ (p k : ℕ) [Fact p.Prime], Odd p → 5 ≤ p ^ k →
    ∀ t : PSL(2, GaloisField p k), orderOf t = 2 →
      ∃ n : ℕ, (2 * n = p ^ k - 1 ∨ 2 * n = p ^ k + 1) ∧
        Nonempty (centralizer ({t} : Set (PSL(2, GaloisField p k))) ≃* DihedralGroup n)

/-- "In `L₂(q)` and `PGL₂(q)` fours groups are self-centralizing" (Bender §3). -/
def L2FourGroupProp : Prop :=
  ∀ (p k : ℕ) [Fact p.Prime], Odd p → 5 ≤ p ^ k →
    (∀ V : Subgroup (PSL(2, GaloisField p k)), IsFourGroup V →
        centralizer (V : Set (PSL(2, GaloisField p k))) = V) ∧
    (∀ V : Subgroup (PGL(2, GaloisField p k)), IsFourGroup V →
        centralizer (V : Set (PGL(2, GaloisField p k))) = V)

/-- 1.7(ii) for `L₀ = L₂(q)`: the TI tori. `Q` has order `q` with `N(Q)` Frobenius of order
`q(q-1)/2`, and the two cyclic tori of orders `(q ± 1)/2` have dihedral normalizers. -/
def L2TIProp : Prop :=
  ∀ (p k : ℕ) [Fact p.Prime], Odd p → 5 ≤ p ^ k →
    ∃ Q Tp Tm : Subgroup (PSL(2, GaloisField p k)),
      Nat.card Q = p ^ k ∧ 2 * Nat.card Tp = p ^ k + 1 ∧ 2 * Nat.card Tm = p ^ k - 1 ∧
      IsCyclic Tp ∧ IsCyclic Tm ∧ (∀ x ∈ Q, x ^ p = 1) ∧
      (∀ g : PSL(2, GaloisField p k), g ∉ normalizer (Q : Set _) →
          Q ⊓ Q.map (MulAut.conj g).toMonoidHom = ⊥) ∧
      (∀ g : PSL(2, GaloisField p k), g ∉ normalizer (Tp : Set _) →
          Tp ⊓ Tp.map (MulAut.conj g).toMonoidHom = ⊥) ∧
      (∀ g : PSL(2, GaloisField p k), g ∉ normalizer (Tm : Set _) →
          Tm ⊓ Tm.map (MulAut.conj g).toMonoidHom = ⊥) ∧
      2 * Nat.card (normalizer (Q : Set (PSL(2, GaloisField p k)))) = p ^ k * (p ^ k - 1) ∧
      Nonempty (normalizer (Tp : Set (PSL(2, GaloisField p k))) ≃* DihedralGroup (Nat.card Tp)) ∧
      Nonempty (normalizer (Tm : Set (PSL(2, GaloisField p k))) ≃* DihedralGroup (Nat.card Tm))

end Work.L2F

/-! ## The add-on Prop statements (verbatim from `_design_gw/Core2.lean` §G, namespace `GW2`) -/

namespace Work.L2F

/-- `s` inverts the subgroup `K`.  (Same definition as `GW2.Inverts` in the design file.) -/
def Inverts {G : Type*} [Group G] (s : G) (K : Subgroup G) : Prop :=
  ∀ x ∈ K, s * x * s⁻¹ = x⁻¹

/-- 1.10(i) in `L₂(q)` (B81 p. 218: "obviously holds"). -/
def L2CentInvariantProp : Prop :=
  ∀ (p k : ℕ) [Fact p.Prime], Odd p → 5 ≤ p ^ k →
    ∀ t : PSL(2, GaloisField p k), orderOf t = 2 → ∀ (r : ℕ) [Fact r.Prime], r ≠ 2 →
      ∀ P : Subgroup (PSL(2, GaloisField p k)), IsPGroup r P →
        centralizer ({t} : Set _) ≤ normalizer (P : Set _) → P ≤ centralizer ({t} : Set _)

/-- §4 (1): odd-order subgroups of `C_L(t)` are cyclic and inverted by an involution of
`C_L(t)` (the dihedral group `D_{q±1}`). -/
def L2CentOddCyclicProp : Prop :=
  ∀ (p k : ℕ) [Fact p.Prime], Odd p → 5 ≤ p ^ k →
    ∀ t : PSL(2, GaloisField p k), orderOf t = 2 → ∀ Y : Subgroup (PSL(2, GaloisField p k)),
      Y ≤ centralizer ({t} : Set _) → Odd (Nat.card Y) →
        IsCyclic Y ∧ ∃ s ∈ centralizer ({t} : Set (PSL(2, GaloisField p k))), orderOf s = 2 ∧
          Inverts s Y

/-- Thm 2.6 step 2: in `PGL₂(q)`, take an involution `t ∈ L = L₂(q)` and an involution `s ∉ L`
commuting with it, and set `R = [t, C_L(s)]`, `R* = [t, C_L(ts)]`.  Both are cyclic of the odd
order `(q+ε)/2`, where `q ≡ ε (mod 4)`, both are inverted by `t`, and `⟨t, R, R*⟩` has order
divisible by 4. -/
def PGL2CommutatorTorusProp : Prop :=
  ∀ (p k : ℕ) [Fact p.Prime], Odd p → 5 ≤ p ^ k →
    ∀ t s : PGL(2, GaloisField p k), orderOf t = 2 → orderOf s = 2 → t * s = s * t →
      t ∈ (Matrix.ProjectiveSpecialLinearGroup.toPGL :
        PSL(2, GaloisField p k) →* PGL(2, GaloisField p k)).range →
      s ∉ (Matrix.ProjectiveSpecialLinearGroup.toPGL :
        PSL(2, GaloisField p k) →* PGL(2, GaloisField p k)).range →
      let L := (Matrix.ProjectiveSpecialLinearGroup.toPGL :
        PSL(2, GaloisField p k) →* PGL(2, GaloisField p k)).range
      let R := ⁅zpowers t, L ⊓ centralizer ({s} : Set _)⁆
      let R' := ⁅zpowers t, L ⊓ centralizer ({t * s} : Set _)⁆
      let m := if p ^ k % 4 = 1 then (p ^ k + 1) / 2 else (p ^ k - 1) / 2
      IsCyclic R ∧ IsCyclic R' ∧ Nat.card R = m ∧ Nat.card R' = m ∧ Inverts t R ∧ Inverts t R' ∧
        4 ∣ Nat.card (zpowers t ⊔ R ⊔ R' : Subgroup _)

/-- §4 (11): number of subgroups of odd prime order `r ∣ (q ± 1)/2` in `L₂(q)`.
For `r ∣ (q+ε)/2`, `ε = ±1`, it is `q(q−ε)/2`. -/
def L2PrimeSubgroupCountProp : Prop :=
  ∀ (p k : ℕ) [Fact p.Prime], Odd p → 5 ≤ p ^ k → ∀ (r : ℕ), r.Prime → r ≠ 2 → r ≠ p →
    ∀ ε : ℤ, (ε = 1 ∨ ε = -1) → (r : ℤ) ∣ ((p ^ k : ℕ) + ε) / 2 →
      2 * ({Y : Subgroup (PSL(2, GaloisField p k)) | Nat.card Y = r}.ncard : ℤ) =
        (p ^ k : ℕ) * ((p ^ k : ℕ) - ε)

/-- §4 (11)/(12): for an odd prime `r ∤ q`, a subgroup `Y` of order `r` has a cyclic centralizer
of order `(q±1)/2` and a dihedral normalizer of order `q±1`. -/
def L2TorusNormalizerProp : Prop :=
  ∀ (p k : ℕ) [Fact p.Prime], Odd p → 5 ≤ p ^ k → ∀ (r : ℕ), r.Prime → r ≠ 2 → r ≠ p →
    ∀ Y : Subgroup (PSL(2, GaloisField p k)), Nat.card Y = r →
      IsCyclic (centralizer (Y : Set (PSL(2, GaloisField p k)))) ∧
      (2 * Nat.card (centralizer (Y : Set (PSL(2, GaloisField p k)))) = p ^ k + 1 ∨
        2 * Nat.card (centralizer (Y : Set (PSL(2, GaloisField p k)))) = p ^ k - 1) ∧
      Nonempty (normalizer (Y : Set (PSL(2, GaloisField p k))) ≃*
        DihedralGroup (Nat.card (centralizer (Y : Set (PSL(2, GaloisField p k))))))

/-- §4 (12): a subgroup of order `r ∤ q` (`r` odd) normalizes at most two subgroups of order `q`. -/
def L2NormalizesTwoSylowProp : Prop :=
  ∀ (p k : ℕ) [Fact p.Prime], Odd p → 5 ≤ p ^ k → ∀ (r : ℕ), r.Prime → r ≠ 2 → r ≠ p →
    ∀ Y : Subgroup (PSL(2, GaloisField p k)), Nat.card Y = r →
      {Q : Subgroup (PSL(2, GaloisField p k)) | Nat.card Q = p ^ k ∧
          Y ≤ normalizer (Q : Set (PSL(2, GaloisField p k)))}.ncard ≤ 2

end Work.L2F

/-! ## The `Core10C4` add-on Prop (lead request, 2026-10-04, design pass 10) -/

namespace Work.L2F

/-- Sylow 2-subgroups are cyclic or dihedral (copied verbatim from `Contracts2.lean`,
namespace `GW2`, where it is called `DihOrCycSylow`). -/
def DihOrCycSylow (G : Type*) [Group G] [Finite G] : Prop :=
  ∀ P : Sylow 2 G, IsCyclic P ∨ ∃ n : ℕ, Nonempty ((P : Subgroup G) ≃* DihedralGroup n)

/-- **`L2OuterInvolutionProp`** (copied verbatim from `_design_gw/Core10C4.lean`).

Let `L ⊴ Q` with `L ≅ L₂(q)`, `Q` with dihedral or cyclic Sylow 2-subgroups, and `r ∈ Q` an
involution not in `L C_Q(L)`.  Then `C_L(r)` contains a cyclic subgroup `R` of order `k'`, the odd
one of `(q ± 1)/2`, and every involution of `C_L(r)` inverts `R`.  (By `AutL2Prop`, `r` is then a
`PGL₂(q) ∖ L₂(q)` involution, and `C_L(r) ≅ D_{2k'}`.) -/
def L2OuterInvolutionProp : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q] (L : Subgroup Q) (p e : ℕ) [Fact p.Prime], Odd p →
    5 ≤ p ^ e → L.Normal → Nonempty (L ≃* PSL(2, GaloisField p e)) → DihOrCycSylow Q →
    ∀ r : Q, orderOf r = 2 → r ∉ L ⊔ centralizer (L : Set Q) →
    ∀ k' : ℕ, Odd k' → (2 * k' = p ^ e + 1 ∨ 2 * k' = p ^ e - 1) →
      ∃ R : Subgroup Q, R ≤ L ∧ R ≤ centralizer ({r} : Set Q) ∧ Nat.card R = k' ∧
        IsCyclic R ∧ ∀ x ∈ L, orderOf x = 2 → x * r = r * x → Inverts x R

end Work.L2F
