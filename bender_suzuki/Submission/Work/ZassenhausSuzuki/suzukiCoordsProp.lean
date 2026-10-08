import Mathlib
import Submission.Work.ZassenhausSuzuki.CoreV3
import Submission.Work.ZassenhausSuzuki.unitMulTheta
import Submission.Work.ZassenhausSuzuki.suzukiFProp
import Submission.Work.ZassenhausSuzuki.frel_torus_all
import Submission.Work.ZassenhausSuzuki.frel_spread
import Submission.Work.ZassenhausSuzuki.frel_center
import Submission.Work.ZassenhausSuzuki.frel_center_aux
import Submission.Work.ZassenhausSuzuki.structPair_sq_aux
import Submission.Work.ZassenhausSuzuki.odd_orderOf_of_isTitsTheta
import Submission.Work.ZassenhausSuzuki.Xval_eq_sigma_Xrep
import Submission.Work.RankOneUniqueness.f_exists
import Submission.Work.RankOneUniqueness.f_unique

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ZassenhausSuzuki.suzukiCoordsProp` — the corrected `f`-half of the Suzuki core

**Status: proved** (no `unproved`; axioms `propext`, `Classical.choice`, `Quot.sound`).

## Build layout (import-cycle note)

`exists_unit_mul_theta` lives in the leaf module `Submission.Work.ZassenhausSuzuki.unitMulTheta`
(imported here and by `frel_center_aux`, which uses it): it used to be defined in this file, but
`frel_center_aux` — imported below — needs it, so keeping it here made this file and
`frel_center_aux` import each other.  The definition moved to the leaf module; the statement and
name are unchanged, and the single import line of `frel_center_aux` was repointed (the only edit
outside this file).

## Route (as implemented)

`structure_value` (`frel_center`, HB 11.12) gives `μ` with `e ρ = h_μ⟨1,1⟩` for the structure
element `ρ = (structPair hsplit).2`; `structPair_sq_aux` gives `ρ² = s`, so `ρ` satisfies the
structure equation, and in the twisted coordinates `e₁ = h_{μ⁻¹} ∘ e` (`torusCoords_twist`) we
have `e₁ ρ = ⟨1,1⟩`; `frel_eq_sigma_of_normalised` (proved below, from `frel_spread` and
`Xval_eq_sigma_Xrep`) then says the book's map in the `e₁`-coordinates *is* `σ`; undoing the
twist (`σ ∘ h_λ = h_{λ⁻¹} ∘ σ`, `sigma_hLam`) gives (★) with `ν = μ²`, and
`suzukiCoords_twist_reduce` (`exists_sq_root`) turns (★) into the statement.

`SuzukiCoordsProp` (`CoreV3.lean`) says: given an admissible coordinatisation `e` of the root
group `Q` by `A(GF(2ᵐ), θ)` with `θ` Tits (the two-point stabiliser `D = H ∩ Hᵗ` acting through
the standard torus `Λ = h(Kˣ)` — `TorusCoords`), there is another admissible coordinatisation
`e'` in which the book's map `f` (`FRel H t x y`, i.e. `t x t = m · t · y`) is the Suzuki map
`τ = SzA.sigma θ`.

## The mathematics

`f` does not change when the coordinates are changed; what changes is the map
`α := e ∘ f ∘ e⁻¹ : A(K,θ)^# → A(K,θ)^#` computed in the new coordinates.  Twisting the
coordinates by `μ ∈ Kˣ` (`e ↦ h_μ ∘ e`, `torusCoords_twist`) conjugates `α` by `h_μ`, and
since `σ ∘ h_λ = h_{λ⁻¹} ∘ σ` (`SzA.sigma_hLam`) one computes
`(h_μ ∘ α ∘ h_μ⁻¹) = h_{μ²} · α · …`; in particular if `α = h_ν ∘ σ` then the twist by `μ`
with `μ² = ν⁻¹` produces `σ` (squares are onto `Kˣ` because `|Kˣ| = 2ᵐ - 1` is odd).
Hence the content of `SuzukiCoordsProp` is

> **(★)** in the coordinates `e`, the book's map `f` is a *twist* of the Suzuki map:
> there is `ν ∈ Kˣ` with `f x = e.symm (h_ν (σ (e x)))` for all `x ∈ Q^#`.

By the classification of Zassenhaus groups (Suzuki 1962 / HB III XI §11 / BG §5) this is a
theorem, and the proof is the Suzuki computation, which we reproduce along HB III XI §11
(the character-free part, with `Fix(θ) = 𝔽₂` free because `θ` is assumed Tits):

* **H1–H6** (Peterfalvi II Ch. VII §1; HB XI 11.10): the canonical maps
  `t x t = β(x) γ(x) t α(x)` (`α = f`, `β = g`, `γ = h`) of `Work.ZassenhausPSL2.Canon`
  satisfy `α(α x) = x`, `β(x)⁻¹ = α(x⁻¹)`, `γ(x⁻¹) = γ(x)`, `α(β x) = γ(x)⁻¹α(x)⁻¹γ(x)`,
  the torus-equivariance `α(d x d⁻¹) = d⁻¹α(x)d`, `γ(d x d⁻¹) = d⁻²γ(x)`, and the *Hua
  equation* `α(x₁x₂) = γ(x₂)·α(α(x₁)β(x₂))·γ(x₂)⁻¹·α(x₂)`.
  (Delegated: `Submission.Work.ZassenhausSuzuki.canon_relations`.)
* **the full torus acts on `Q`** (`Work.ZassenhausSuzuki.frel_torus_all`, **proved**):
  `D → Kˣ` is bijective (`|D| = #Inv(Q) = |K|-1 = |Kˣ|` plus faithfulness), so H3/H4 hold for
  every `λ ∈ Kˣ`.
* **the `Λ`-orbits of `A(K,θ)^#`** (`orbit_classification` below, **proved**): every `x ≠ 1` is
  `Λ`-conjugate to `⟨0,1⟩` or to `⟨1,c⟩` (`c ∈ K`), i.e. the invariant `c = b / a^{1+θ}`
  classifies the orbits.  This is the "Suzuki partition" input of BG 5.16–5.17 / HB XI 11.11b.
* **the value of `f` on the centre of `Q`**, i.e. `f(⟨0,b⟩) = ⟨ν·b/θb, 0⟩` for a single
  `ν ∈ Kˣ` (BG 5.20(a) / HB XI 11.12; delegated: `frel_center`).  This is the input the *Tits*
  half of the area (`suzukiTitsOfFix`) needs as well.
* **the structure equation** (Suzuki 1962 Prop. 9–12; `Work.ThmF.ChV12.structureIdentity`,
  *proved* in the workspace): there is a unique pair `(s,ρ)` with `s ∈ Q` an involution and
  `t s t = ρ t ρ⁻¹`; in the notation above this says `α(s) = ρ⁻¹`, `β(s)γ(s) = ρ`.
* **the computation** (HB XI 11.11c–11.14): H1–H6 + the centre value + the orbit
  classification determine `α` as a twist of `σ` — the remaining mathematical work of the area,
  BG 5.18–5.20 / HB XI 11.11–11.14.

## Status

Proved here: `exists_unit_mul_theta`, `orbit_classification`, `exists_sq_root`,
`suzukiCoords_twist_reduce` (the twist-normalisation: `SuzukiCoordsProp`'s conclusion follows
from (★)).  Proved elsewhere (imported): `frel_torus_all`; proved by colleagues:
`canon_relations` (H1–H6); in flight: `frel_center`.

**Remaining: exactly (★).**  Route (HB III XI §11, all inputs now available):

1. `α(s) = ρ⁻¹` for the distinguished pair `(s,ρ)` of `structureIdentity` — immediate from the
   `Canon.spec` (`t s t = β(s)γ(s)·t·α(s) = ρ·t·ρ⁻¹` and uniqueness of the canonical form).
2. HB 11.11a: `ρ⁻¹h₁⁻¹ρh₁ ≠ ρ⁻¹h₂⁻¹ρh₂` for distinct `h₁,h₂ ∈ D` — from `dStab_fpf_on_Q`
   (a non-trivial `h` centralising `ρ ≠ 1` would fix a point of `Q#`).
3. HB 11.11b: the `Λ`-orbit classification in the `ρ`-form — use `orbit_classification` plus the
   explicit coordinates of `ρ⁻¹h⁻¹ρh`.
4. **HB 11.11c (the crux computation)**: for `h ∈ D ∖ {1}` acting as `h_μ`, with `k = h_ν`
   determined by `ν(νθ) = μ²(μθ)² + μ(μθ)`,
   `α(ρ⁻¹h⁻¹ρh) = k·ρ⁻¹k⁻¹·hρh⁻¹`.
   This is a *concrete formula* (not a rewording of (★)) and is the right next delegation; its
   proof is one carefully chosen application of H6 plus the structure equation, exactly as in
   HB XI 11.11c (p. 273 of the book).
5. HB 11.12–11.13 then give `α` on all of `A(K,θ)^#` via the orbit classification (2)+(3)+(4),
   and comparison with `σ` (whose values on the same representatives are explicit, see
   `SzA.sigma`) yields (★) — this last comparison is where the single `ν` of (★) appears.

### Derivation of the HB 11.12 step (for the prover of `structure_value` / `frel_center`)

Write `e(s) = ⟨0,c⟩` (`c ≠ 0`) and `e(ρ) = ⟨a,b⟩`.  For `λ ∈ Kˣ ∖ {1}` put

`z(λ) := ρ⁻¹ · (h_λ ρ h_λ⁻¹)`  (the element `g⁻¹h⁻¹gh` of HB XI 11.11),

which in coordinates is

`z(λ) = ⟨a(1+λ), b(1+λθλ) + aθa(1+θλ)⟩`

(explicit product in `A(K,θ)`: `SzA.mul_a`, `SzA.mul_b`, `SzA.inv_a`, `SzA.inv_b`).  Hence its
`Λ`-orbit invariant `z.b/(z.a·θ z.a)` equals the invariant `b/(aθa)` of `ρ` **iff**

`(1+λ)/(1+θλ) = 1 + aθa/b`.

By HB 11.11a the `z(λ)` are pairwise non-conjugate, and by HB 11.11b none of them is
`Λ`-conjugate to `ρ` (nor to `s`), so the displayed equation has no solution `λ ∈ K ∖ {0,1}`;
since `λ ↦ (1+λ)/(1+θλ)` is a bijection of `K ∖ {0,1}` onto `K ∖ {0,1}` (a Möbius map fixing
`0,1`; this is where `Fix θ = 𝔽₂`, i.e. `θ` Tits, enters, exactly as in HB 11.12), the value
`1 + aθa/b` must be `0` or `1`, i.e. `a = 0` or `b = aθa`.  The second alternative is the
desired conclusion `ρ ~ ⟨1,1⟩` (`h_μ⟨1,1⟩ = ⟨μ,μθμ⟩`, and `λ ↦ λθλ` is onto by
`exists_unit_mul_theta`); the first (`ρ ∈ Z(Q)`) is excluded because then `ρ` would be an
involution of `Q` commuting with `s` and `t s t = ρ t ρ⁻¹`, forcing `ρ = s = 1` by the
uniqueness in `structureIdentity`.  This is exactly HB XI 11.12, and it is what `frel_center`'s
prover has left to do (`structure_value`).

`frel_center` (the centre case of (★)) is the input the *Tits* half of the area needs
(`suzukiFixTheta` / `suzukiTitsOfFix`) and is being proved in parallel.
-/

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.ZassenhausSuzuki

open Work.ZassenhausSuzuki.SzA

/-! ## The Λ-orbits of `A(K,θ)^#` -/

/-- **The `Λ`-orbits of `A(K,θ)^#`.**  For a Tits endomorphism `θ` every non-identity element
of Higman's group is `Λ = h(Kˣ)`-conjugate to `⟨0,1⟩` (the centre `Z(A)^#`) or to `⟨1,c⟩`
(`c ∈ K`, the orbit of `⟨1,0⟩` being `c = 0`).  The invariant is `c = b/(a·θ a)`. -/
theorem orbit_classification {K : Type} [Field K] [CharP K 2] {θ : K ≃+* K}
    (hθ : IsTitsTheta θ) (x : SzA K θ) (hx : x ≠ 1) :
    (∃ lam : Kˣ, x = hLam θ (lam : K) (⟨0, 1⟩ : SzA K θ)) ∨
      (∃ (c : K) (lam : Kˣ), x = hLam θ (lam : K) (⟨1, c⟩ : SzA K θ)) := by
  rcases eq_or_ne (x.a) 0 with ha | ha
  · left
    have hb : x.b ≠ 0 := by
      intro hb
      exact hx (by ext <;> simp [ha, hb])
    obtain ⟨lam, hlam⟩ := exists_unit_mul_theta hθ (Units.mk0 x.b hb)
    refine ⟨lam, ?_⟩
    ext <;> simp [hLam, hlam, ha]
  · right
    have hne : x.a * θ x.a ≠ 0 := mul_ne_zero ha (θ.map_ne_zero_iff.mpr ha)
    have hb : x.a * θ x.a * (x.b / (x.a * θ x.a)) = x.b := by
      rw [mul_div_assoc', div_eq_iff hne]; ring
    refine ⟨x.b / (x.a * θ x.a), Units.mk0 x.a ha, ?_⟩
    ext
    · simp [hLam]
    · simpa [hLam] using hb.symm

/-! ## The twist-normalisation step of the assembly -/

/-- **Squares are onto `Kˣ`** for a finite field of characteristic two: `x ↦ x²` is injective
(`x² = y²` gives `(x - y)² = 0` in characteristic two, so `x = y`) on the finite set `K`, hence
surjective on `K` and therefore on `Kˣ`. -/
theorem exists_sq_root {K : Type} [Field K] [Finite K] [CharP K 2] (ν : Kˣ) :
    ∃ μ : Kˣ, μ * μ = ν := by
  -- in characteristic two the only solution of `u * u = 1` in `Kˣ` is `u = 1`
  have hne : ∀ u : Kˣ, u * u = 1 → u = 1 := by
    intro u hu
    have hu' : (u : K) * (u : K) = 1 := by
      simpa using congrArg (fun w : Kˣ => (w : K)) hu
    have hfac : ((u : K) - 1) * ((u : K) + 1) = 0 := by
      calc ((u : K) - 1) * ((u : K) + 1) = (u : K) * (u : K) - 1 := by ring
        _ = 0 := by rw [hu', sub_self]
    rcases mul_eq_zero.mp hfac with h1 | h1
    · exact Units.ext (sub_eq_zero.mp h1)
    · refine Units.ext ?_
      have h2 : (u : K) = -1 := (add_eq_zero_iff_eq_neg.mp h1)
      rw [h2, CharTwo.neg_eq]
      simp
  have hinj : Function.Injective (fun μ : Kˣ => μ * μ) := by
    intro a b hab
    have hab' : a * a = b * b := hab
    have h1 : (a * b⁻¹) * (a * b⁻¹) = 1 := by
      rw [mul_mul_mul_comm, hab']
      group
    exact mul_inv_eq_one.mp (hne (a * b⁻¹) h1)
  exact Finite.injective_iff_surjective.mp hinj ν

/-- **The twist-normalisation step.**  If in the coordinates `e` the book's map `f` is a twist
`h_ν ∘ σ` of the Suzuki map `σ` (`FRel H t x (e.symm (h_ν (σ (e x))))` for all `x ≠ 1`), then
the coordinates `e' = (h_μ) ∘ e` with `μ² = ν⁻¹` (which exist by `exists_sq_root`) are again
admissible (`TorusCoords`, by `torusCoords_twist`) and satisfy the conclusion of
`SuzukiCoordsProp`: in them the book's map is `σ` itself.  (Conjugating by `h_μ` sends `σ` to
`h_{μ⁻²}σ` because `σ ∘ h_λ = h_{λ⁻¹} ∘ σ`.) -/
theorem suzukiCoords_twist_reduce {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    {K : Type} [Field K] [Finite K] [CharP K 2] {θ : K ≃+* K} (hθ : IsTitsTheta θ)
    (e : Q ≃* SzA K θ) (htorus : TorusCoords K θ H Q t e)
    (hα : ∃ ν : Kˣ, ∀ x : Q, x ≠ 1 →
      Work.RankOneUniqueness.FRel H t (x : G)
        (((e.symm (hLam θ (ν : K) (SzA.sigma θ (e x))) : Q) : G))) :
    ∃ e' : Q ≃* SzA K θ, TorusCoords K θ H Q t e' ∧
      ∀ x : Q, x ≠ 1 →
        Work.RankOneUniqueness.FRel H t (x : G)
          (((e'.symm (SzA.sigma θ (e' x)) : Q) : G)) := by
  obtain ⟨ν, hν⟩ := hα
  obtain ⟨μ, hμ⟩ := exists_sq_root (K := K) ν⁻¹
  refine ⟨e.trans (SzA.hLamHom θ μ), torusCoords_twist htorus μ, fun x hx => ?_⟩
  have harg : ((SzA.hLamHom θ μ : MulAut (SzA K θ)).symm
      (SzA.sigma θ ((SzA.hLamHom θ μ : MulAut (SzA K θ)) (e x))))
      = hLam θ (ν : K) (SzA.sigma θ (e x)) := by
    have hfsym : ((SzA.hLamHom θ μ) : MulAut (SzA K θ)).symm = SzA.hLamHom θ μ⁻¹ :=
      map_inv (SzA.hLamHom θ) μ
    rw [hfsym, SzA.hLamHom_apply, SzA.hLamHom_apply]
    rw [sigma_hLam θ hθ μ]
    rw [← SzA.hLam_mul]
    congr 1
    have hval : (μ : K) * (μ : K) = ((ν⁻¹ : Kˣ) : K) := by
      simpa using congrArg (fun u : Kˣ => (u : K)) hμ
    rw [Units.val_inv_eq_inv_val, ← mul_inv, hval, Units.val_inv_eq_inv_val, inv_inv]
  rw [MulEquiv.symm_trans_apply, MulEquiv.trans_apply, harg]
  exact hν x hx

/-! ## The coordinate computation of `ρ⁻¹ (h_λ ρ h_λ⁻¹)` (HB XI 11.11)

The element `z(λ) = ρ⁻¹·(h_λ ρ h_λ⁻¹)` of HB XI 11.11 (`ρ` the structure element of
`Work.ThmF.ChV12.structureIdentity`, `h_λ ∈ D`) is used in HB 11.11b/c and in the orbit
comparison of HB 11.12; its coordinates are computed here once, in the form needed by those
arguments.  Note `h_λ ρ h_λ⁻¹ = h_λ (ρ)` in the coordinates `e` (`TorusCoords`), so this is a
computation inside `A(K,θ)`. -/

/-- **The element `z(λ) = ρ⁻¹·h_λ(ρ)` in coordinates.**  For `ρ = ⟨a,b⟩` and `λ ∈ Kˣ`,

`ρ⁻¹ · h_λ(ρ) = ⟨a(1+λ), b(1+λθλ) + a·θa·(1+θλ)⟩`.

This is the explicit form of HB XI 11.11's `g⁻¹h⁻¹gh` (with `h = h_{λ⁻¹}`), and of
`g^{-1}h^{-1}gh` in HB 11.12; the `Λ`-orbit invariant of the right hand side equals
`b/(a·θa)` exactly when `(1+λ)/(1+θλ) = 1 + a·θa/b`. -/
theorem zLam_eq {K : Type} [Field K] [CharP K 2] (θ : K ≃+* K) (a b : K) (lam : Kˣ) :
    (⟨a, b⟩ : SzA K θ)⁻¹ * SzA.hLam θ (lam : K) ⟨a, b⟩
      = (⟨a * (1 + (lam : K)),
          b * (1 + (lam : K) * θ (lam : K)) + a * θ a * (1 + θ (lam : K))⟩ : SzA K θ) := by
  ext <;>
    simp only [SzA.mul_a, SzA.mul_b, SzA.inv_a, SzA.inv_b, SzA.hLam_a, SzA.hLam_b, map_mul,
      map_one, CharTwo.neg_eq] <;>
    ring

end Work.ZassenhausSuzuki

namespace Work.ZassenhausSuzuki

/-! ## The normalisation `e g = ⟨1,1⟩`: the book's map is the Suzuki map -/

/-- **HB III XI 11.13 (a)+(b) together with HB 11.11, in the normalisation `e g = ⟨1,1⟩`.**

If in the coordinates `e` the structure element `g` (`t·g²·t = g·t·g⁻¹`, `g² ∈ Q`) has
coordinates `⟨1,1⟩`, then the book's map `f` (`FRel H t x y`) is the Suzuki map `σ` on all of
`Q^#`: `f x = e.symm (σ (e x))`.

The `D`-orbit representatives of `Q^#` are `e.symm ⟨0,1⟩`, `e.symm ⟨1,1⟩`, `e.symm ⟨1,0⟩` and the
generic ones `e.symm (Xrep θ ν)` (`ν ≠ 1`), on which the book's map is known
(`frel_spread`, HB 11.13 (a)+(b) = `frel_structure_values` and `frel_generic_value_eps`); since
`σ` takes on those representatives the values `⟨1,0⟩`, `⟨1,1⟩`, `⟨0,1⟩` and — by the field
identity `Xval_eq_sigma_Xrep` (which is where Tits-ness `θ² =` Frobenius enters) — `Xval θ ν ξ`,
the two maps agree at all representatives; both are anti-equivariant under the torus
(`frel_torus_inv` for `f`, `SzA.sigma_hLam` for `σ`), so they agree everywhere. -/
theorem frel_eq_sigma_of_normalised {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hsplit : Submission.Blueprint.IsSplitRankOne H Q t)
    (hzass : Submission.Blueprint.IsZassenhaus H) (h2 : IsPGroup 2 Q)
    {m : ℕ} {θ : GaloisField 2 m ≃+* GaloisField 2 m} (hθ : IsTitsTheta θ)
    {e : Q ≃* SzA (GaloisField 2 m) θ}
    (htorus : TorusCoords (GaloisField 2 m) θ H Q t e)
    {g : Q} (hg : e g = (⟨1, 1⟩ : SzA (GaloisField 2 m) θ))
    (hstruct : t * (((g ^ 2 : Q)) : G) * t = (g : G) * t * (((g⁻¹ : Q)) : G)) :
    ∀ x : Q, x ≠ 1 → Work.RankOneUniqueness.FRel H t (x : G)
      (((e.symm (SzA.sigma θ (e x)) : Q) : G)) := by
  intro x hx
  obtain ⟨lam, v, w, hex, hrel, hcase⟩ :=
    frel_spread hsplit hzass h2 hθ.1 (odd_orderOf_of_isTitsTheta hθ) htorus hg hstruct x hx
  have hw : w = SzA.sigma θ v := by
    rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨nu, xi, hxi, hnu, rfl, rfl⟩
    · ext <;> simp [SzA.sigma, SzA.N, CharTwo.add_self_eq_zero]
    · ext <;> simp [SzA.sigma, SzA.N, CharTwo.add_self_eq_zero]
    · ext <;> simp [SzA.sigma, SzA.N, CharTwo.add_self_eq_zero]
    · exact Xval_eq_sigma_Xrep θ hθ nu xi hnu hxi
  rw [hw] at hrel
  have hσ : SzA.sigma θ (e x) = SzA.hLam θ (((lam : (GaloisField 2 m)ˣ) : GaloisField 2 m))⁻¹
      (SzA.sigma θ v) := by
    rw [hex, sigma_hLam θ hθ lam, Units.val_inv_eq_inv_val]
  rw [hσ]
  exact hrel

/-- **`SuzukiCoordsProp`** (the corrected `f`-half of the Suzuki core).

Route.  Let `(s,ρ)` be the structure-identity pair of `Work.ThmF.ChV12.structureIdentity`
(`t s t = ρ t ρ⁻¹`) and `μ` the unit with `e ρ = h_μ ⟨1,1⟩` (`structure_value`, BG 5.20(a) /
HB 11.12).  Then `ρ² = s` (`structPair_sq_aux`), so with the structure element `g := ρ` the
structure equation `t g² t = g t g⁻¹` holds, and in the twisted coordinates
`e₁ := h_{μ⁻¹} ∘ e` we have `e₁ ρ = ⟨1,1⟩`, so by `frel_eq_sigma_of_normalised` the book's map
*is* the Suzuki map in the `e₁`-coordinates.  Undoing the twist (`σ ∘ h_μ = h_{μ⁻¹} ∘ σ`) shows
that in the original coordinates the book's map is `h_{μ²} ∘ σ` — exactly (★), which
`suzukiCoords_twist_reduce` converts into the statement. -/
theorem suzukiCoordsProp : Work.ZassenhausSuzuki.SuzukiCoordsProp := by
  intro G _ _ hG H Q t hsplit hzass m θ hθ e htorus
  -- `Q` is a 2-group
  have h2 : IsPGroup 2 Q := isPGroup_two_of_mulEquiv θ e
  -- the structure-identity pair and its coordinates
  obtain ⟨μ, hμ⟩ := structure_value hsplit hzass hθ e htorus
  obtain ⟨hsQ, _hs2, hρQ, hspec⟩ := structPair_spec hsplit
  have ht2 : t * t = 1 := ht_mul_self hsplit
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hρsq : (structPair hsplit).2 * (structPair hsplit).2 = (structPair hsplit).1 :=
    structPair_sq_aux hsplit hzass hθ e htorus h2
  -- the structure equation for the element `g := ρ`
  have hstruct : t * ((((⟨(structPair hsplit).2, hρQ⟩ : Q) ^ 2 : Q)) : G) * t
      = ((⟨(structPair hsplit).2, hρQ⟩ : Q) : G) * t
        * ((((⟨(structPair hsplit).2, hρQ⟩ : Q))⁻¹ : Q) : G) := by
    have hp : ((⟨(structPair hsplit).2, hρQ⟩ : Q) ^ 2 : Q)
        = (⟨(structPair hsplit).1, hsQ⟩ : Q) := by
      apply Subtype.ext
      simpa [Subgroup.coe_pow, pow_two] using hρsq
    rw [hp]
    show t * (structPair hsplit).1 * t = (structPair hsplit).2 * t * (structPair hsplit).2⁻¹
    rw [← hspec, htinv]
  -- the twisted coordinates, in which `e₁ ρ = ⟨1,1⟩`
  have htor₁ : TorusCoords (GaloisField 2 m) θ H Q t (e.trans (SzA.hLamHom θ μ⁻¹)) :=
    torusCoords_twist htorus μ⁻¹
  have hg : (e.trans (SzA.hLamHom θ μ⁻¹)) ⟨(structPair hsplit).2, hρQ⟩
      = (⟨1, 1⟩ : SzA (GaloisField 2 m) θ) := by
    show SzA.hLam θ (((μ⁻¹ : (GaloisField 2 m)ˣ)) : GaloisField 2 m)
      (e ⟨(structPair hsplit).2, hρQ⟩) = ⟨1, 1⟩
    rw [hμ, ← SzA.hLam_mul]
    have h : (((μ⁻¹ : (GaloisField 2 m)ˣ)) : GaloisField 2 m) * ((μ : (GaloisField 2 m)ˣ) : GaloisField 2 m)
        = 1 := by simp
    rw [h, SzA.hLam_one]
  have hall := frel_eq_sigma_of_normalised hsplit hzass h2 hθ htor₁ hg hstruct
  -- (★): in the original coordinates the book's map is `h_{μ²} ∘ σ`, so
  -- `suzukiCoords_twist_reduce` converts the normalised statement into the target
  refine suzukiCoords_twist_reduce hθ e htorus ⟨μ * μ, fun x hx => ?_⟩
  have hkey : ((e.trans (SzA.hLamHom θ μ⁻¹)).symm
        (SzA.sigma θ ((e.trans (SzA.hLamHom θ μ⁻¹)) x)) : Q)
      = (e.symm (SzA.hLam θ (((μ * μ : (GaloisField 2 m)ˣ)) : GaloisField 2 m)
          (SzA.sigma θ (e x))) : Q) := by
    have hcoe : (((SzA.hLamHom θ μ⁻¹) : MulAut (SzA (GaloisField 2 m) θ))).symm
        = SzA.hLamHom θ μ := by
      apply MulEquiv.ext
      intro y
      rw [MulEquiv.symm_apply_eq, SzA.hLamHom_apply, SzA.hLamHom_apply, ← SzA.hLam_mul]
      have h1 : (((μ⁻¹ : (GaloisField 2 m)ˣ)) : GaloisField 2 m)
          * ((μ : (GaloisField 2 m)ˣ) : GaloisField 2 m) = 1 := by simp
      rw [h1, SzA.hLam_one]
    rw [MulEquiv.symm_trans_apply, MulEquiv.trans_apply, hcoe, SzA.hLamHom_apply,
      SzA.hLamHom_apply, sigma_hLam θ hθ μ⁻¹, inv_inv, ← SzA.hLam_mul, ← Units.val_mul]
  rw [← hkey]
  exact hall x hx

end Work.ZassenhausSuzuki
