import Mathlib
import Submission.Work.ZassenhausSuzuki.TitsAux
import Submission.Work.ZassenhausSuzuki.frel_torus_inv

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `frel_axis`: the book's map `f` at the axis point `(u,0)`

Let `(G,H,Q,t)` be the split rank-one (Zassenhaus) configuration, `Q ≅ A(K,θ)` via the
coordinatisation `e` (`K = GF(2ᵐ)`), and let `f` be the map determined by the book's relation
`FRel H t x y` (`t x t = m · t · y`, `m ∈ H`; Peterfalvi II Ch. VII §1).

Given the **structure equation** `t g² t = g t g⁻¹` for an element `g ∈ Q` with
`e g = (1,1)` — so that `e (g⁻¹) = (1,0)`, `e (g²) = (0,1)`, i.e. `g²` is the central
involution `(0,1) ∈ Z(A(K,θ))` and `g` the "axis" element `(1,d)` with `d = 1` — the value of
`f` at the whole torus orbit of `(1,0)` is determined:

`f (u, 0) = (0, u⁻¹ · θ u⁻¹)`.

The proof has two ingredients, both proved elsewhere in the area:

* the structure equation gives `FRel H t (g²) (g⁻¹)` with witness `g ∈ Q ≤ H`, hence
  `FRel H t (g⁻¹) (g²)` because `f` is an involution (`frel_symm`);
* `f` is `Λ`-equivariant up to inversion — `f (h_λ x) = h_{λ⁻¹} (f x)`
  (`frel_torus_inv`) — and every `λ ∈ Kˣ` is realised by an element of the two-point
  stabiliser `D = H ∩ Hᵗ` (`exists_torus_action`).

Applying the equivariance with `λ = u` to `f (g⁻¹) = g²` and using
`h_u (1,0) = (u,0)`, `h_{u⁻¹} (0,1) = (0, u⁻¹·θu⁻¹)` gives the claim.
-/

set_option autoImplicit false

namespace Work.ZassenhausSuzuki

open Submission.Blueprint

theorem frel_axis {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hsplit : Submission.Blueprint.IsSplitRankOne H Q t)
    (hzass : Submission.Blueprint.IsZassenhaus H) (h2 : IsPGroup 2 Q)
    {m : ℕ} {θ : GaloisField 2 m ≃+* GaloisField 2 m}
    {e : Q ≃* Work.ZassenhausSuzuki.SzA (GaloisField 2 m) θ}
    (htorus : ∀ d : G, d ∈ Submission.Blueprint.twoPoint H t →
      ∃ lam : (GaloisField 2 m)ˣ, ∀ x : Q,
        ∃ y : Q, (y : G) = d * (x : G) * d⁻¹ ∧
          e y = Work.ZassenhausSuzuki.SzA.hLam θ (lam : GaloisField 2 m) (e x))
    {g : Q} (hg : e g = (⟨1, 1⟩ : Work.ZassenhausSuzuki.SzA (GaloisField 2 m) θ))
    (hstruct : t * (((g ^ 2 : Q)) : G) * t = (g : G) * t * (((g⁻¹ : Q)) : G))
    {u : GaloisField 2 m} (hu : u ≠ 0) :
    Work.RankOneUniqueness.FRel H t
      (((e.symm (⟨u, 0⟩ : Work.ZassenhausSuzuki.SzA (GaloisField 2 m) θ)) : Q) : G)
      (((e.symm (⟨0, u⁻¹ * θ u⁻¹⟩ : Work.ZassenhausSuzuki.SzA (GaloisField 2 m) θ)) : Q) : G) := by
  classical
  -- `Q` is nontrivial: `g` has `e`-image `(1,1) ≠ 1`
  have hQ : Q ≠ ⊥ := by
    intro hbot
    have hg1 : (g : Q) = 1 := Subtype.ext (Subgroup.mem_bot.mp (hbot ▸ g.2))
    have he1 : e g = 1 := by rw [hg1, map_one]
    rw [hg] at he1
    have h10 : (1 : GaloisField 2 m) = 0 := by
      simpa using congrArg Work.ZassenhausSuzuki.SzA.a he1
    exact one_ne_zero h10
  -- some `d ∈ D = H ∩ Hᵗ` realises the torus element `h_u` on `Q`
  obtain ⟨d, hd, hact⟩ :=
    Work.ZassenhausSuzuki.exists_torus_action hsplit hzass htorus (Units.mk0 u hu)
  -- the structure equation reads `FRel H t (g²) (g⁻¹)`, with witness `g ∈ Q ≤ H`
  have hbase : Work.RankOneUniqueness.FRel H t ((g⁻¹ : Q) : G) (((g ^ 2 : Q)) : G) :=
    Work.ZassenhausSuzuki.frel_symm hsplit ⟨(g : G), hsplit.le g.2, hstruct⟩
  -- coordinates of `g⁻¹` and `g²`
  have hgi : e (g⁻¹ : Q) = (⟨1, 0⟩ : Work.ZassenhausSuzuki.SzA (GaloisField 2 m) θ) := by
    rw [map_inv, hg]
    ext <;> simp [CharTwo.neg_eq, CharTwo.add_self_eq_zero]
  have hgj : e ((g ^ 2 : Q)) = (⟨0, 1⟩ : Work.ZassenhausSuzuki.SzA (GaloisField 2 m) θ) := by
    rw [map_pow, hg, pow_two]
    ext <;> simp [CharTwo.add_self_eq_zero]
  -- `Λ`-equivariance of `f` at `λ = u`
  have hkey := Work.ZassenhausSuzuki.frel_torus_inv hsplit hzass hQ h2 θ e hd
    (Units.mk0 u hu) hact hbase
  -- `h_u (1,0) = (u,0)` and `h_{u⁻¹} (0,1) = (0, u⁻¹·θu⁻¹)`
  have h1 : Work.ZassenhausSuzuki.SzA.hLam θ (↑(Units.mk0 u hu) : GaloisField 2 m)
        (e (g⁻¹ : Q)) = (⟨u, 0⟩ : Work.ZassenhausSuzuki.SzA (GaloisField 2 m) θ) := by
    rw [hgi]
    ext <;> simp
  have h2' : Work.ZassenhausSuzuki.SzA.hLam θ (↑((Units.mk0 u hu)⁻¹) : GaloisField 2 m)
        (e ((g ^ 2 : Q))) = (⟨0, u⁻¹ * θ u⁻¹⟩ : Work.ZassenhausSuzuki.SzA (GaloisField 2 m) θ) := by
    rw [hgj]
    ext <;> simp [Units.val_inv_eq_inv_val]
  rw [h1, h2'] at hkey
  exact hkey

end Work.ZassenhausSuzuki
