import Mathlib
import Submission.Work.PiS.Interfaces
import Submission.Work.RatHurewicz.RelHomotopy
import Submission.Work.Cohomology.CupRing
import Submission.Work.Cohomology.Pullback
import Submission.Work.Serre.Models
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option synthInstance.maxHeartbeats 400000

/-!
# pi6_sphere_three_mulEquiv_zmod_twelve — the lead's interface (DO NOT EDIT: every `Prop` is a contract)

Target: `π₆(S³) ≃* ℤ/12`.  Route (blueprint `REFS/NOTES_LEAD_PI6.md`): Serre's killing tower
`Z → Y → E → S³` (`E = S³⟨3⟩`, `Y = S³⟨4⟩`, `Z = S³⟨5⟩`, each the homotopy fibre of a Postnikov
section), integral and mod-2 range exact sequences, the low-degree homology of `K(ℤ/2,n)` (from a
multiplicative mod-p Serre spectral sequence), the homology of `E` (integral Wang sequence), and ONE
Steenrod-square input (`SqCyclicCore`, i.e. `Sq²Sq²ι₃ ≠ 0`) for the non-split extension `ℤ/4`.

Areas (each ONE lemma; an area takes other areas' `Prop`s as hypotheses; the final proof is the
composition `Work.Pi6.pi6_of_areas` in `Wiring.lean`):
* `BasepointMulEquiv`, `TowerPi`, `SerreRangeLES`            — homotopy/homology glue;
* `MSSHolds`                                                — the multiplicative Serre SS (crux B);
* `K2ZFacts`, `EMMod2`, `EMOdd`                             — forcing computations (assume `MSSHolds`);
* `EFacts`                                                  — `H_*(S³⟨3⟩)` (Wang + `K2ZFacts`);
* `SqCyclicCore`, `EMExp`                                   — Steenrod-lite consequences (crux A);
* `EMTableZ`, `SqCyclic`, `HomologyAlg`                     — assembly layers.

Conventions: singular (co)homology of `TopCat.of X` with coefficients in a commutative ring `R`
(`Work.Cohomology.singularChains R`, `Work.Cohomology.singularCohomology R`); homotopy groups are
Mathlib's `HomotopyGroup` (cube model).  `K(A,n)` models are the library's range models
`Work.Serre.IsEMSpaceUpTo A n _ N X x` (π_n ≅ A, other π_i = 0 for i ≤ N).
-/

set_option autoImplicit false

open CategoryTheory CategoryTheory.Limits

namespace Work.Pi6

noncomputable section

/-! ## Vocabulary -/

/-- The challenge's space `S³ ⊆ ℝ⁴` (`Work.PiS.Sph 3` unfolds to the challenge's sphere). -/
abbrev S3 : Type := Work.PiS.Sph 3

/-- The base point `e₀ = (1,0,0,0)`. -/
abbrev s3 : S3 := Work.PiS.pt 3

/-- Singular homology `H_i(X;R)`. -/
abbrev HR (R : Type) [CommRing R] (X : Type) [TopologicalSpace X] (i : ℕ) : ModuleCat R :=
  (Work.Cohomology.singularChains R (TopCat.of X)).homology i

/-- `f_* : H_i(X;R) → H_i(Y;R)`. -/
abbrev hmap (R : Type) [CommRing R] {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (i : ℕ) : HR R X i ⟶ HR R Y i :=
  HomologicalComplex.homologyMap
    (Work.Cohomology.chainMap R (TopCat.of X) (TopCat.of Y) (TopCat.ofHom f)) i

/-- Singular cohomology `H^n(X;R)`. -/
abbrev Coh (R : Type) [CommRing R] (X : Type) [TopologicalSpace X] (n : ℕ) : ModuleCat R :=
  Work.Cohomology.singularCohomology R n (TopCat.of X)

/-- `f^* : H^n(Y;R) → H^n(X;R)`. -/
abbrev cmap (R : Type) [CommRing R] {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) (n : ℕ) : Coh R Y n ⟶ Coh R X n :=
  Work.Cohomology.singularCohomologyMap R (TopCat.of X) (TopCat.of Y) (TopCat.ofHom f) n

/-- The cup product `H^n(X;R) × H^m(X;R) → H^{n+m}(X;R)` (the library's `cupH'`). -/
abbrev cup (R : Type) [CommRing R] (X : Type) [TopologicalSpace X] (n m : ℕ) :
    Coh R X n →ₗ[R] Coh R X m →ₗ[R] Coh R X (n + m) :=
  Work.Cohomology.cupH' R (TopCat.toSSet.obj (TopCat.of X)) n m

/-- The unit `1 ∈ H⁰(X;R)`. -/
abbrev one (R : Type) [CommRing R] (X : Type) [TopologicalSpace X] : Coh R X 0 :=
  Work.Cohomology.oneH R (TopCat.toSSet.obj (TopCat.of X))

/-- Cup powers of a degree-2 class: `cpow x k = x^k ∈ H^{2k}`. -/
def cpow {R : Type} [CommRing R] {X : Type} [TopologicalSpace X] (x : Coh R X 2) :
    (k : ℕ) → Coh R X (2 * k)
  | 0 => one R X
  | k + 1 => cup R X (2 * k) 2 (cpow x k) x

/-- Output of a Postnikov section (`Work.Serre.serrePostnikovTower_strong`): `g : Y → P` is
bijective on `π_i` at every base point for `i ≤ m`, and `π_i(P) = 0` for `m < i ≤ N`.  (`y₀` only
fixes which base point the tower uses downstream.) -/
def PostnikovData (m N : ℕ) {Y P : Type} [TopologicalSpace Y] [TopologicalSpace P]
    (g : C(Y, P)) (_y₀ : Y) : Prop :=
  (∀ i : ℕ, i ≤ m → ∀ y : Y, Function.Bijective (Work.Serre.piMapN g i y)) ∧
    ∀ i : ℕ, m < i → i ≤ N → ∀ p : P, Subsingleton (HomotopyGroup (Fin i) P p)

/-- The cover `E = S³⟨3⟩ = hofib(g₃ : S³ → P₃)`. -/
abbrev Ecov {P3 : Type} [TopologicalSpace P3] (g3 : C(S3, P3)) : Type :=
  Work.RatHurewicz.homotopyFibre g3 s3

/-- Base point of `E`. -/
abbrev e0 {P3 : Type} [TopologicalSpace P3] (g3 : C(S3, P3)) : Ecov g3 :=
  Work.RatHurewicz.homotopyFibreBasepoint g3 s3

/-- The cover `Y = S³⟨4⟩ = hofib(g₄ : E → P₄)`. -/
abbrev Ycov {P3 P4 : Type} [TopologicalSpace P3] [TopologicalSpace P4] (g3 : C(S3, P3))
    (g4 : C(Ecov g3, P4)) : Type :=
  Work.RatHurewicz.homotopyFibre g4 (e0 g3)

/-- Base point of `Y`. -/
abbrev y0 {P3 P4 : Type} [TopologicalSpace P3] [TopologicalSpace P4] (g3 : C(S3, P3))
    (g4 : C(Ecov g3, P4)) : Ycov g3 g4 :=
  Work.RatHurewicz.homotopyFibreBasepoint g4 (e0 g3)

/-- The cover `Z = S³⟨5⟩ = hofib(g₅ : Y → P₅)`. -/
abbrev Zcov {P3 P4 P5 : Type} [TopologicalSpace P3] [TopologicalSpace P4] [TopologicalSpace P5]
    (g3 : C(S3, P3)) (g4 : C(Ecov g3, P4)) (g5 : C(Ycov g3 g4, P5)) : Type :=
  Work.RatHurewicz.homotopyFibre g5 (y0 g3 g4)

/-! ## Homotopy-side areas -/

/-- **Area BASEPT.** π₆ of `S³` does not depend on the base point, as a group. -/
def BasepointMulEquiv : Prop :=
  ∀ x : S3, Nonempty (HomotopyGroup.Pi 6 S3 x ≃* HomotopyGroup.Pi 6 S3 s3)

/-- **Area TOWER.** For any Postnikov data of the tower: (1) `π₆(S³) ≃* H₆(Z;ℤ)` (the tower
projections are π₆-isomorphisms, and Hurewicz for the 5-connected `Z`); (2) connectivity of `E`, `Y`,
`Z`; (3)/(4) the Postnikov sections `P₄`, `P₅` are `K(ℤ/2,·)` range models as soon as the first
homology group of `E`, resp. `Y`, is `ℤ/2`. -/
def TowerPi : Prop :=
  ∀ (P3 : Type) [TopologicalSpace P3] (g3 : C(S3, P3)), PostnikovData 3 12 g3 s3 →
  ∀ (P4 : Type) [TopologicalSpace P4] (g4 : C(Ecov g3, P4)), PostnikovData 4 12 g4 (e0 g3) →
  ∀ (P5 : Type) [TopologicalSpace P5] (g5 : C(Ycov g3 g4, P5)),
    PostnikovData 5 12 g5 (y0 g3 g4) →
      Nonempty (HomotopyGroup.Pi 6 S3 s3 ≃* Multiplicative (HR ℤ (Zcov g3 g4 g5) 6)) ∧
      (∀ i : ℕ, i ≤ 3 → Subsingleton (HomotopyGroup (Fin i) (Ecov g3) (e0 g3))) ∧
      (∀ i : ℕ, i ≤ 4 → Subsingleton (HomotopyGroup (Fin i) (Ycov g3 g4) (y0 g3 g4))) ∧
      (∀ i : ℕ, i ≤ 5 → Subsingleton (HomotopyGroup (Fin i) (Zcov g3 g4 g5)
        (Work.RatHurewicz.homotopyFibreBasepoint g5 (y0 g3 g4)))) ∧
      (Nonempty (HR ℤ (Ecov g3) 4 ≃ₗ[ℤ] ZMod 2) →
        Work.Serre.IsEMSpaceUpTo (ZMod 2) 4 (by norm_num) 12 P4 (g4 (e0 g3))) ∧
      (Nonempty (HR ℤ (Ycov g3 g4) 5 ≃ₗ[ℤ] ZMod 2) →
        Work.Serre.IsEMSpaceUpTo (ZMod 2) 5 (by norm_num) 12 P5 (g5 (y0 g3 g4)))

/-! ## Serre exact sequence in the stable range (any coefficients) -/

/-- **Area SRANGE.** For a Serre fibration `p : E → B` with `B` `(b-1)`-connected (`b ≥ 2`) and fibre
`F = p⁻¹(p e₀)` path connected with `H_j(F;ℤ) = 0` for `0 < j < f`, the Serre exact sequence
`H_{i+1}(F;R) → H_{i+1}(E;R) → H_{i+1}(B;R) → H_i(F;R) → H_i(E;R)` is exact for `i + 1 < b + f`,
for EVERY commutative ring `R` (ℤ: `Work.StemsB.serrePairComparisonTwo` + the pair sequence;
general `R`: free-complex transfer of the relative iso). -/
def SerreRangeLES : Prop :=
  ∀ (R : Type) [CommRing R] (E B : Type) [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B))
    (e₀ : E) (b f : ℕ), Work.StemsB.IsSerreFibration p → 2 ≤ b →
    (∀ i : ℕ, i < b → Subsingleton (HomotopyGroup (Fin i) B (p e₀))) →
    Subsingleton (HomotopyGroup (Fin 0) (Work.StemsB.fibre p (p e₀)) ⟨e₀, rfl⟩) →
    (∀ j : ℕ, 0 < j → j < f → IsZero (HR ℤ (Work.StemsB.fibre p (p e₀)) j)) →
    ∃ bd : ∀ i : ℕ, HR R B (i + 1) ⟶ HR R (Work.StemsB.fibre p (p e₀)) i,
      ∀ i : ℕ, i + 1 < b + f →
        Function.Exact (hmap R (Work.StemsB.fibreIncl p (p e₀)) (i + 1)).hom
          (hmap R p (i + 1)).hom ∧
        Function.Exact (hmap R p (i + 1)).hom (bd i).hom ∧
        Function.Exact (bd i).hom (hmap R (Work.StemsB.fibreIncl p (p e₀)) i).hom

/-! ## The multiplicative cohomological Serre spectral sequence over a field (crux B) -/

/-- The page-`r` differential's bidegree `(r, 1 - r)`. -/
def vr (r : ℕ) : ℤ × ℤ := ((r : ℤ), 1 - (r : ℤ))

/-- A first-quadrant cohomological spectral sequence of `𝕜`-modules with a product, pages `r ≥ 2`
(fields at `r < 2` are junk).  Maps are relation-indexed (as in `HomologicalComplex`):
`d r a b` is zero unless `b = a + vr r`, and `mul r a b c h` multiplies `E_r^a × E_r^b → E_r^c`
for `h : a + b = c`.  `proj` presents `E_{r+1}` as cycles modulo boundaries of `E_r`. -/
structure CohSS (𝕜 : Type) [Field 𝕜] where
  E : ℕ → ℤ × ℤ → ModuleCat 𝕜
  d : ∀ (r : ℕ) (a b : ℤ × ℤ), E r a ⟶ E r b
  d_shape : ∀ (r : ℕ) (a b : ℤ × ℤ), b ≠ a + vr r → d r a b = 0
  d_comp : ∀ (r : ℕ) (a b c : ℤ × ℤ), d r a b ≫ d r b c = 0
  quad : ∀ (r : ℕ) (a : ℤ × ℤ), (a.1 < 0 ∨ a.2 < 0) → IsZero (E r a)
  proj : ∀ (r : ℕ) (a : ℤ × ℤ), LinearMap.ker (d r a (a + vr r)).hom →ₗ[𝕜] E (r + 1) a
  proj_surj : ∀ (r : ℕ) (a : ℤ × ℤ), 2 ≤ r → Function.Surjective (proj r a)
  proj_ker : ∀ (r : ℕ) (a : ℤ × ℤ), 2 ≤ r → ∀ x : LinearMap.ker (d r a (a + vr r)).hom,
    proj r a x = 0 ↔ (x : E r a) ∈ LinearMap.range (d r (a - vr r) a).hom
  mul : ∀ (r : ℕ) (a b c : ℤ × ℤ), a + b = c → (E r a →ₗ[𝕜] E r b →ₗ[𝕜] E r c)
  /-- **Coherence of the product in its bidegree index.**  The proof argument of `a + b = c` is
  irrelevant.  Without this field the Leibniz rule (`leibniz` below, whose proof argument is
  `by rw [← h]; abel`) cannot be combined with the multiplicativity clause of `IsSerreMSS` (whose
  proof argument is `by ext <;> simp`): `mul` is arbitrary data and the proof slot is part of the
  term, so no other axiom relates the two instantiations.  For any `mul` that is a conjugated tensor
  multiplication (as in the Serre spectral sequence) this is proof-irrelevance of the instantiation,
  i.e. free.  Needed by every forcing argument (`Work.Pi6.EMM2.k2field` and the areas K2Z, EMM2,
  EMZ, SQASM). -/
  mul_congr : ∀ (r : ℕ) (a b c : ℤ × ℤ) (h₁ h₂ : a + b = c) (x : E r a) (y : E r b),
    mul r a b c h₁ x y = mul r a b c h₂ x y
  leibniz : ∀ (r : ℕ) (a b c : ℤ × ℤ) (h : a + b = c) (x : E r a) (y : E r b), 2 ≤ r →
    (d r c (c + vr r)).hom (mul r a b c h x y) =
      mul r (a + vr r) b (c + vr r) (by rw [← h]; abel) ((d r a (a + vr r)).hom x) y +
        ((-1 : 𝕜) ^ (a.1 + a.2).natAbs) •
          mul r a (b + vr r) (c + vr r) (by rw [← h]; abel) x ((d r b (b + vr r)).hom y)
  proj_mul : ∀ (r : ℕ) (a b c : ℤ × ℤ) (h : a + b = c) (x : LinearMap.ker (d r a (a + vr r)).hom)
    (y : LinearMap.ker (d r b (b + vr r)).hom) (z : LinearMap.ker (d r c (c + vr r)).hom), 2 ≤ r →
    (z : E r c) = mul r a b c h x y → proj r c z = mul (r + 1) a b c h (proj r a x) (proj r b y)
  /-- bottom row: `E_{r+1}^{s,0}` is a quotient of `E_r^{s,0}` (all of `E_r^{s,0}` are cycles). -/
  bot : ∀ (r : ℕ) (s : ℤ), E r (s, 0) ⟶ E (r + 1) (s, 0)
  bot_spec : ∀ (r : ℕ) (s : ℤ) (x : LinearMap.ker (d r (s, 0) ((s, 0) + vr r)).hom), 2 ≤ r →
    (bot r s).hom x = proj r (s, 0) x
  /-- column 0: `E_{r+1}^{0,q}` is the subspace of cycles of `E_r^{0,q}`. -/
  col : ∀ (r : ℕ) (q : ℤ), E (r + 1) (0, q) ⟶ E r (0, q)
  col_spec : ∀ (r : ℕ) (q : ℤ) (x : LinearMap.ker (d r (0, q) ((0, q) + vr r)).hom), 2 ≤ r →
    (col r q).hom (proj r (0, q) x) = x

/-- `E_2^{s,0} → E_{k+2}^{s,0}` (iterated bottom-row quotients). -/
def CohSS.botTo {𝕜 : Type} [Field 𝕜] (S : CohSS 𝕜) (s : ℤ) :
    (k : ℕ) → (S.E 2 (s, 0) ⟶ S.E (k + 2) (s, 0))
  | 0 => 𝟙 _
  | k + 1 => S.botTo s k ≫ S.bot (k + 2) s

/-- `E_{k+2}^{0,q} → E_2^{0,q}` (iterated column-0 inclusions). -/
def CohSS.colTo {𝕜 : Type} [Field 𝕜] (S : CohSS 𝕜) (q : ℤ) :
    (k : ℕ) → (S.E (k + 2) (0, q) ⟶ S.E 2 (0, q))
  | 0 => 𝟙 _
  | k + 1 => S.col (k + 2) q ≫ S.colTo q k

/-- `S` is the Serre spectral sequence of `p` (fibre `F = p⁻¹(p e₀)`) in total degrees `≤ N`:
`E_2^{s,q} ≅ H^s(B) ⊗ H^q(F)` multiplicatively (`(b⊗f)(b'⊗f') = (-1)^{q s'} bb' ⊗ ff'`),
`E_{n+2} = E_∞` in total degree `n` computes `H^n(E)`, and the two edge maps. -/
def IsSerreMSS {𝕜 : Type} [Field 𝕜] (S : CohSS 𝕜) {E B : Type} [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (e₀ : E) (N : ℕ) : Prop :=
  ∃ e2 : ∀ s q : ℕ, s ≤ N → q ≤ N → (S.E 2 ((s : ℤ), (q : ℤ)) ≅
      ModuleCat.of 𝕜 (TensorProduct 𝕜 (Coh 𝕜 B s) (Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q))),
    (∀ (s q s' q' : ℕ) (b : Coh 𝕜 B s) (f : Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q)
        (b' : Coh 𝕜 B s') (f' : Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q')
        (hs : s + s' ≤ N) (hq : q + q' ≤ N),
        S.mul 2 ((s : ℤ), (q : ℤ)) ((s' : ℤ), (q' : ℤ)) (((s + s' : ℕ) : ℤ), ((q + q' : ℕ) : ℤ))
            (by ext <;> simp) ((e2 s q (by omega) (by omega)).inv.hom (b ⊗ₜ f))
            ((e2 s' q' (by omega) (by omega)).inv.hom (b' ⊗ₜ f')) =
          ((-1 : 𝕜) ^ (q * s')) • (e2 (s + s') (q + q') (by omega) (by omega)).inv.hom
            ((cup 𝕜 B s s' b b') ⊗ₜ (cup 𝕜 (Work.StemsB.fibre p (p e₀)) q q' f f'))) ∧
    (∀ n : ℕ, 1 ≤ n → n ≤ N → Subsingleton (Coh 𝕜 E n) →
        ∀ s q : ℕ, s + q = n → IsZero (S.E (n + 2) ((s : ℤ), (q : ℤ)))) ∧
    (∀ n : ℕ, n ≤ N →
        (∑ s ∈ Finset.range (n + 1), Module.finrank 𝕜 (S.E (n + 2) ((s : ℤ), ((n - s : ℕ) : ℤ)))) =
          Module.finrank 𝕜 (Coh 𝕜 E n)) ∧
    (∀ (s : ℕ) (hs : s ≤ N) (b : Coh 𝕜 B s),
        (S.botTo (s : ℤ) s).hom ((e2 s 0 (by omega) (by omega)).inv.hom (b ⊗ₜ one 𝕜 (Work.StemsB.fibre p (p e₀)))) = 0 ↔
          (cmap 𝕜 p s).hom b = 0) ∧
    (∀ (q : ℕ) (hq : q ≤ N) (f : Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q),
        (∃ e : Coh 𝕜 E q, (cmap 𝕜 (Work.StemsB.fibreIncl p (p e₀)) q).hom e = f) ↔
          ∃ z : S.E (q + 2) (0, (q : ℤ)), (S.colTo (q : ℤ) q).hom z =
            (e2 0 q (by omega) (by omega)).inv.hom (one 𝕜 B ⊗ₜ f))

/-- **Area MSS (crux B).** Every Serre fibration over a simply connected base, with fibre and base
of finite type through degree `N`, has a multiplicative Serre spectral sequence over every field.
Route: `REFS/NOTES_LEAD_PI6.md` §MSS. -/
def MSSHolds : Prop :=
  ∀ (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B] (p : C(E, B))
    (e₀ : E) (N : ℕ), Work.StemsB.IsSerreFibration p → Work.PiS.SimplyConn B (p e₀) →
    (∀ q : ℕ, q ≤ N → FiniteDimensional 𝕜 (Coh 𝕜 (Work.StemsB.fibre p (p e₀)) q)) →
    (∀ s : ℕ, s ≤ N → FiniteDimensional 𝕜 (Coh 𝕜 B s)) →
    ∃ S : CohSS 𝕜, IsSerreMSS S p e₀ N

/-! ## Eilenberg–MacLane forcing computations (assume `MSSHolds`) -/

/-- **Area K2Z.** Cohomology of `K(ℤ,2)` range models through degree 9: integrally
`H^{2k} = ℤ·x^k`, `H^{odd} = 0`; over every field `H^{2k} = 𝕜·w^k ≠ 0`, `H^{odd} = 0` (`k ≤ 4`). -/
def K2ZFacts : Prop :=
  ∀ (X : Type) [TopologicalSpace X] (x₀ : X) (N : ℕ), 10 ≤ N →
    Work.Serre.IsEMSpaceUpTo ℤ 2 (by norm_num) N X x₀ →
      (∃ x : Coh ℤ X 2,
        (∀ k : ℕ, k ≤ 4 → ∀ a : Coh ℤ X (2 * k), ∃! n : ℤ, a = n • cpow x k) ∧
        (∀ k : ℕ, k ≤ 4 → Subsingleton (Coh ℤ X (2 * k + 1)))) ∧
      (∀ (𝕜 : Type) [Field 𝕜], ∃ w : Coh 𝕜 X 2,
        ∀ k : ℕ, k ≤ 4 → cpow w k ≠ 0 ∧ Module.finrank 𝕜 (Coh 𝕜 X (2 * k)) = 1 ∧
          Subsingleton (Coh 𝕜 X (2 * k + 1)))

/-- **Area EMM2.** Mod-2 facts for `K(ℤ/2,n)` range models (through `N ≥ 10`), n = 2, 3, 4:
upper bounds on `dim H^q(−;𝔽₂)` and non-vanishing cup squares. -/
def EMMod2 : Prop :=
  (∀ (X : Type) [TopologicalSpace X] (x₀ : X) (N : ℕ), 10 ≤ N →
      Work.Serre.IsEMSpaceUpTo (ZMod 2) 2 (by norm_num) N X x₀ →
      Module.rank (ZMod 2) (Coh (ZMod 2) X 3) ≤ 1 ∧
      (∀ a : Coh (ZMod 2) X 2, a ≠ 0 → cup (ZMod 2) X 2 2 a a ≠ 0) ∧
      (∀ y : Coh (ZMod 2) X 3, y ≠ 0 → cup (ZMod 2) X 3 3 y y ≠ 0)) ∧
  (∀ (X : Type) [TopologicalSpace X] (x₀ : X) (N : ℕ), 10 ≤ N →
      Work.Serre.IsEMSpaceUpTo (ZMod 2) 3 (by norm_num) N X x₀ →
      Module.rank (ZMod 2) (Coh (ZMod 2) X 4) ≤ 1 ∧
      Module.rank (ZMod 2) (Coh (ZMod 2) X 5) ≤ 1 ∧
      (∀ a : Coh (ZMod 2) X 3, a ≠ 0 → cup (ZMod 2) X 3 3 a a ≠ 0)) ∧
  (∀ (X : Type) [TopologicalSpace X] (x₀ : X) (N : ℕ), 10 ≤ N →
      Work.Serre.IsEMSpaceUpTo (ZMod 2) 4 (by norm_num) N X x₀ →
      Module.rank (ZMod 2) (Coh (ZMod 2) X 7) ≤ 2 ∧
      Module.rank (ZMod 2) (Coh (ZMod 2) X 8) ≤ 2)

/-- **Area EMODD.** `K(ℤ/2,n)` (n = 2,3,4) is `𝔽_p`-acyclic through degree 8 for odd primes `p`. -/
def EMOdd : Prop :=
  ∀ (n : ℕ) (hn : 2 ≤ n), n ≤ 4 → ∀ (X : Type) [TopologicalSpace X] (x₀ : X) (N : ℕ), 10 ≤ N →
    Work.Serre.IsEMSpaceUpTo (ZMod 2) n (by omega) N X x₀ →
    ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ i : ℕ, 0 < i → i ≤ 8 → Subsingleton (HR (ZMod p) X i)

/-! ## The 3-connected cover `E = S³⟨3⟩` -/

/-- **Area EFACTS.** `H₄(E) ≅ ℤ/2`, `H₅(E) = 0`, `H₆(E) ≅ ℤ/3`, `H₇(E) = 0`, and the nonzero class of
`H⁴(E;𝔽₂)` has nonzero square. -/
def EFacts : Prop :=
  ∀ (P3 : Type) [TopologicalSpace P3] (g3 : C(S3, P3)), PostnikovData 3 12 g3 s3 →
    Nonempty (HR ℤ (Ecov g3) 4 ≃ₗ[ℤ] ZMod 2) ∧ Subsingleton (HR ℤ (Ecov g3) 5) ∧
    Nonempty (HR ℤ (Ecov g3) 6 ≃ₗ[ℤ] ZMod 3) ∧ Subsingleton (HR ℤ (Ecov g3) 7) ∧
    (∀ u : Coh (ZMod 2) (Ecov g3) 4, u ≠ 0 → cup (ZMod 2) (Ecov g3) 4 4 u u ≠ 0)

/-! ## Steenrod-lite consequences (crux A) -/

/-- **Area SQ (part 1, crux A).** `Sq²Sq²ι₃ ≠ 0`, Steenrod-free form: a based map `h : K → L` from a
`K(ℤ/2,3)` to a `K(ℤ/2,5)` which is nonzero on `H⁵(−;𝔽₂)` is nonzero on `H⁷(−;𝔽₂)`. -/
def SqCyclicCore : Prop :=
  ∀ (K L : Type) [TopologicalSpace K] [TopologicalSpace L] (k₀ : K) (l₀ : L) (N : ℕ), 11 ≤ N →
    Work.Serre.IsEMSpaceUpTo (ZMod 2) 3 (by norm_num) N K k₀ →
    Work.Serre.IsEMSpaceUpTo (ZMod 2) 5 (by norm_num) N L l₀ →
    ∀ h : C(K, L), h k₀ = l₀ → cmap (ZMod 2) h 5 ≠ 0 → cmap (ZMod 2) h 7 ≠ 0

/-- **Area SQ (part 2).** Exponent facts (`Sq¹Sq² = Sq³` via the Bockstein): `H₅(K(ℤ/2,3);ℤ)` and
`H₇(K(ℤ/2,4);ℤ)` contain an element of order ≤ 2 which is not divisible by 2 (models through
`N ≥ 10`, resp. `N ≥ 12`: the proof loops twice down to `K(ℤ/2,2)`). -/
def EMExp : Prop :=
  (∀ (X : Type) [TopologicalSpace X] (x₀ : X) (N : ℕ), 10 ≤ N →
      Work.Serre.IsEMSpaceUpTo (ZMod 2) 3 (by norm_num) N X x₀ →
      ∃ a : HR ℤ X 5, (2 : ℤ) • a = 0 ∧ ∀ b : HR ℤ X 5, (2 : ℤ) • b ≠ a) ∧
  (∀ (X : Type) [TopologicalSpace X] (x₀ : X) (N : ℕ), 12 ≤ N →
      Work.Serre.IsEMSpaceUpTo (ZMod 2) 4 (by norm_num) N X x₀ →
      ∃ a : HR ℤ X 7, (2 : ℤ) • a = 0 ∧ ∀ b : HR ℤ X 7, (2 : ℤ) • b ≠ a)

/-! ## Assembly layers -/

/-- **Area EMZ.** Integral tables: for `K(ℤ/2,4)`: `H₆ ≅ ℤ/2`, `H₇ ≅ ℤ/2`, `dim H₈(−;𝔽₂) ≤ 2`;
for `K(ℤ/2,5)`: `H₆ = 0`, `H₇ ≅ ℤ/2` (range models through `N ≥ 12`). -/
def EMTableZ : Prop :=
  (∀ (X : Type) [TopologicalSpace X] (x₀ : X) (N : ℕ), 12 ≤ N →
      Work.Serre.IsEMSpaceUpTo (ZMod 2) 4 (by norm_num) N X x₀ →
      Nonempty (HR ℤ X 6 ≃ₗ[ℤ] ZMod 2) ∧ Nonempty (HR ℤ X 7 ≃ₗ[ℤ] ZMod 2) ∧
      Module.rank (ZMod 2) (HR (ZMod 2) X 8) ≤ 2) ∧
  (∀ (X : Type) [TopologicalSpace X] (x₀ : X) (N : ℕ), 12 ≤ N →
      Work.Serre.IsEMSpaceUpTo (ZMod 2) 5 (by norm_num) N X x₀ →
      Subsingleton (HR ℤ X 6) ∧ Nonempty (HR ℤ X 7 ≃ₗ[ℤ] ZMod 2))

/-- **Area SQASM.** The cyclicity input: `g₅ : Y → P₅` is nonzero on `H₇(−;𝔽₂)`. -/
def SqCyclic : Prop :=
  ∀ (P3 : Type) [TopologicalSpace P3] (g3 : C(S3, P3)), PostnikovData 3 12 g3 s3 →
  ∀ (P4 : Type) [TopologicalSpace P4] (g4 : C(Ecov g3, P4)), PostnikovData 4 12 g4 (e0 g3) →
  ∀ (P5 : Type) [TopologicalSpace P5] (g5 : C(Ycov g3 g4, P5)),
    PostnikovData 5 12 g5 (y0 g3 g4) →
    Work.Serre.IsEMSpaceUpTo (ZMod 2) 4 (by norm_num) 12 P4 (g4 (e0 g3)) →
    Work.Serre.IsEMSpaceUpTo (ZMod 2) 5 (by norm_num) 12 P5 (g5 (y0 g3 g4)) →
    hmap (ZMod 2) g5 7 ≠ 0

/-- **Area HALG.** The homology algebra of the tower: (B) `H₅(Y) ≅ ℤ/2` once `P₄` is a `K(ℤ/2,4)`;
(C) `H₆(Z;ℤ)` is cyclic of order 12 once also `P₅` is a `K(ℤ/2,5)` and `g₅` is nonzero on
`H₇(−;𝔽₂)`. -/
def HomologyAlg : Prop :=
  ∀ (P3 : Type) [TopologicalSpace P3] (g3 : C(S3, P3)), PostnikovData 3 12 g3 s3 →
  ∀ (P4 : Type) [TopologicalSpace P4] (g4 : C(Ecov g3, P4)), PostnikovData 4 12 g4 (e0 g3) →
    Work.Serre.IsEMSpaceUpTo (ZMod 2) 4 (by norm_num) 12 P4 (g4 (e0 g3)) →
    Nonempty (HR ℤ (Ycov g3 g4) 5 ≃ₗ[ℤ] ZMod 2) ∧
    ∀ (P5 : Type) [TopologicalSpace P5] (g5 : C(Ycov g3 g4, P5)),
      PostnikovData 5 12 g5 (y0 g3 g4) →
      Work.Serre.IsEMSpaceUpTo (ZMod 2) 5 (by norm_num) 12 P5 (g5 (y0 g3 g4)) →
      hmap (ZMod 2) g5 7 ≠ 0 →
      IsAddCyclic (HR ℤ (Zcov g3 g4 g5) 6) ∧ Nat.card (HR ℤ (Zcov g3 g4 g5) 6) = 12

/-- **The core statement** (at the base point `s3`, default group structure). -/
def Pi6Core : Prop := Nonempty (HomotopyGroup.Pi 6 S3 s3 ≃* Multiplicative (ZMod 12))

end

end Work.Pi6
