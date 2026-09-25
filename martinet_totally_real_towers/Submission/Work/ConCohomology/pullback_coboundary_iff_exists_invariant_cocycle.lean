/-
Copyright: the martinet_totally_real_towers team.

# Cochains: `ker(inf₂) = im(tg)` (Hochschild--Serre exactness at `H²(Q,M)`)

Fix a group extension `1 → N → G → Q → 1` (`GroupExt G Q N`), a section `s : Q → G` of `q`, a
discrete `Q`-module `M` whose `G`-action factors through `q`
(`hcompG : ∀ g m, g • m = E.q g • m`), and `N` acting trivially on `M` (`hcompN`).

For a `2`-cocycle `c` on `Q`, the pullback `c ∘ (q × q)` is a coboundary on `G` **iff** `c` differs
from the transgression `tg(φ)` of a `G`-invariant `1`-cocycle `φ` on `N` by a coboundary on `Q`:

`(∃ b : G → M, c ∘ (q × q) = d¹b) ↔ ∃ φ (G-invariant 1-cocycle on N) (∃ w : Q → M, tg φ - c = d¹w)`.

This is the cochain-level form of `ker(inf₂) = im(tg)`, the exactness of the five term sequence
`0 → H¹(Q,M) → H¹(G,M) → H¹(N,M)^Q →^{tg} H²(Q,M) →^{inf} H²(G,M)`
at `H²(Q,M)`.

The two directions are proved by explicit cocycle computations.

* (⇐) `q_pullback_tgFun_is_coboundary` exhibits `β` with `d¹β = (tg φ) ∘ (q × q)`; then
  `β - (w ∘ q)` is a coboundary on `G` whose differential is `tg φ ∘ (q × q) - (d¹w) ∘ (q × q)`,
  and `d¹(w ∘ q) = (d¹w) ∘ (q × q)` because the `G`-action factors through `q` (`hcompG`).
* (⇒) given `b` with `c ∘ (q × q) = d¹b`, put `φ n = b 1 - b (i n)` and `w y = -b (s y)`; then
  `φ` is additive and `G`-equivariant (both pure group identities inside `G`), and the
  transgression identity is the associativity computation
  `b 1 - b (a z⁻¹) + b a = b z` for `a = s y₁ s y₂`, `z = s (y₁ y₂)` with `q a = q z`.
-/

import Mathlib
import Submission.Work.ConCohomology.Extension
import Submission.Work.ConCohomology.q_pullback_tgFun_is_coboundary

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Work.ConCohomology

open Function Classical

section PullbackCoboundary

variable {G Q N : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
variable [Group N] [TopologicalSpace N] [IsTopologicalGroup N]
variable {M : Type*} [AddCommGroup M] [DistribMulAction G M] [DistribMulAction N M]
variable [DistribMulAction Q M]

/-- `d¹` is additive, in subtraction form. -/
private lemma d1Fun_sub (f g : G → M) : d1Fun (f - g) = d1Fun f - d1Fun g := by
  funext p
  obtain ⟨x, y⟩ := p
  simp only [d1Fun_apply, Pi.sub_apply]
  rw [smul_sub]
  abel

namespace GroupExt

/-- The projection of `i n` is trivial. -/
private lemma q_i (E : GroupExt G Q N) (n : N) : E.q (E.i n) = 1 := (E.ker_eq (E.i n)).mpr ⟨n, rfl⟩

end GroupExt

/-- Since the `G`-action on `M` factors through `q`, `d¹` commutes with pulling back along `q`. -/
private lemma d1Fun_comp_q (E : GroupExt G Q N) (hcompG : ∀ (g : G) (m : M), g • m = E.q g • m)
    (w : Q → M) :
    d1Fun (G := G) (fun x : G => w (E.q x)) =
      fun p : G × G => d1Fun (G := Q) w (E.q p.1, E.q p.2) := by
  funext p
  obtain ⟨x, y⟩ := p
  simp only [d1Fun_apply]
  rw [hcompG x (w (E.q y)), map_mul]

/-- **`ker(inf₂) = im(tg)` at the level of cochains.**  A `2`-cocycle `c` on `Q` is a coboundary
after pulling back along `q : G → Q` if and only if `c` is the transgression of an invariant
`1`-cocycle on `N`, up to a coboundary on `Q`. -/
theorem pullback_coboundary_iff_exists_invariant_cocycle {G Q N : Type*} [Group G]
    [TopologicalSpace G] [IsTopologicalGroup G] [Group Q] [TopologicalSpace Q]
    [IsTopologicalGroup Q] [Group N] [TopologicalSpace N] [IsTopologicalGroup N]
    {M : Type*} [AddCommGroup M] [DistribMulAction G M] [DistribMulAction N M]
    [DistribMulAction Q M] (E : GroupExt G Q N) (hcompN : ∀ (n : N) (m : M), n • m = m)
    (hcompG : ∀ (g : G) (m : M), g • m = E.q g • m)
    (s : Q → G) (hs : ∀ y : Q, E.q (s y) = y)
    (c : Q × Q → M) (hc : IsCocycle2 c) :
    (∃ b : G → M, (fun p : G × G => c (E.q p.1, E.q p.2)) = d1Fun (G := G) b) ↔
      ∃ (φ : N → M) (_hφ : IsCocycle1 φ)
        (_hinv : ∀ (g : G) (n : N), φ (E.conj g n) = g • φ n),
        ∃ w : Q → M, tgFun E s hs φ - c = d1Fun (G := Q) w := by
  constructor
  · -- (⇒): given `b` with `c ∘ (q × q) = d¹b`, produce `φ n = b 1 - b (i n)` and `w y = -b (s y)`.
    rintro ⟨b, hb⟩
    have hb' : ∀ x y : G, c (E.q x, E.q y) = x • b y - b (x * y) + b x := fun x y => by
      have h := congrFun hb (x, y)
      simpa only [d1Fun_apply] using h
    -- the "normalisation" `c (1, y) = b 1`
    have hc1 : ∀ y : Q, c (1, y) = b 1 := by
      intro y
      have h := hb' 1 (s y)
      rw [map_one, hs y, one_smul, one_mul] at h
      rw [h, sub_self, zero_add]
    -- multiplicativity of `b` along `i`
    have hii : ∀ m n : N, b (E.i m * E.i n) = b (E.i n) - b 1 + b (E.i m) := by
      intro m n
      have h := hb' (E.i m) (E.i n)
      rw [GroupExt.q_i E m, GroupExt.q_i E n, hc1 1, hcompG (E.i m) (b (E.i n)),
        GroupExt.q_i E m, one_smul] at h
      rw [h]
      abel
    refine ⟨fun n : N => b 1 - b (E.i n), ?_, ?_, fun y : Q => -(b (s y)), ?_⟩
    · -- `φ` is additive (a `1`-cocycle for the trivial action of `N`)
      intro m n
      show b 1 - b (E.i (m * n)) = (b 1 - b (E.i m)) + m • (b 1 - b (E.i n))
      rw [map_mul, hii m n, hcompN m (b 1 - b (E.i n))]
      abel
    · -- `φ` is `G`-equivariant
      intro g n
      show b 1 - b (E.i (E.conj g n)) = g • (b 1 - b (E.i n))
      have h1 : b (E.i n * g⁻¹) = b g⁻¹ - b 1 + b (E.i n) := by
        have h := hb' (E.i n) g⁻¹
        rw [GroupExt.q_i E n, map_inv] at h
        rw [hc1 ((E.q g)⁻¹), hcompG (E.i n) (b g⁻¹), GroupExt.q_i E n, one_smul] at h
        rw [h]
        abel
      have h2 : b (g * (E.i n * g⁻¹)) = g • b (E.i n * g⁻¹) - c (E.q g, (E.q g)⁻¹) + b g := by
        have h := hb' g (E.i n * g⁻¹)
        rw [map_mul, GroupExt.q_i E n, map_inv, one_mul] at h
        rw [h]
        abel
      have h3 : b 1 = g • b g⁻¹ - c (E.q g, (E.q g)⁻¹) + b g := by
        have h := hb' g g⁻¹
        rw [map_inv, mul_inv_cancel] at h
        rw [h]
        abel
      have hA : b (g * (E.i n * g⁻¹)) = b 1 - g • b 1 + g • b (E.i n) := by
        calc b (g * (E.i n * g⁻¹))
            = g • (b g⁻¹ - b 1 + b (E.i n)) - c (E.q g, (E.q g)⁻¹) + b g := by rw [h2, h1]
          _ = (g • b g⁻¹ - c (E.q g, (E.q g)⁻¹) + b g) + (g • b (E.i n) - g • b 1) := by
                rw [smul_add, smul_sub]
                abel
          _ = b 1 - g • b 1 + g • b (E.i n) := by
                rw [h3]
                abel
      rw [E.i_conj, mul_assoc, hA, smul_sub]
      abel
    · -- the transgression identity `tg(φ) - c = d¹w`
      funext p
      obtain ⟨y1, y2⟩ := p
      have hkey' : ∀ a z : G, E.q a = E.q z → b 1 - b (a * z⁻¹) + b a = b z := by
        intro a z hqz
        have hA : b (a * z⁻¹) = a • b z⁻¹ - c (E.q z, (E.q z)⁻¹) + b a := by
          have h := hb' a z⁻¹
          rw [map_inv, hqz] at h
          rw [h]
          abel
        have hB : b z = b 1 - z • b z⁻¹ + c (E.q z, (E.q z)⁻¹) := by
          have h := hb' z z⁻¹
          rw [map_inv, mul_inv_cancel] at h
          rw [h]
          abel
        have hsmul : a • b z⁻¹ = z • b z⁻¹ := by rw [hcompG a, hcompG z, hqz]
        rw [hA, hB, hsmul]
        abel
      have hfin : b 1 - b (s y1 * s y2 * (s (y1 * y2))⁻¹) + b (s y1 * s y2)
          = b (s (y1 * y2)) :=
        hkey' (s y1 * s y2) (s (y1 * y2)) (by rw [map_mul, hs y1, hs y2, hs (y1 * y2)])
      have hc_s : c (y1, y2) = s y1 • b (s y2) - b (s y1 * s y2) + b (s y1) := by
        have h := hb' (s y1) (s y2)
        rwa [hs y1, hs y2] at h
      simp only [Pi.sub_apply, tgFun_eq_tgArg]
      rw [i_tgArg E s hs y1 y2, d1Fun_apply, hc_s, hcompG (s y1) (b (s y2)), hs y1,
        smul_neg, ← hfin]
      abel
  · -- (⇐): a transgression differing from `c` by a coboundary gives a coboundary on `G`.
    rintro ⟨φ, hφ, hinv, w, hw⟩
    obtain ⟨β, hβ⟩ := q_pullback_tgFun_is_coboundary E hcompN s hs φ hφ hinv
    refine ⟨β - fun x : G => w (E.q x), ?_⟩
    rw [d1Fun_sub, ← hβ, d1Fun_comp_q E hcompG w]
    funext p
    have h := congrFun hw (E.q p.1, E.q p.2)
    simp only [Pi.sub_apply] at h ⊢
    rw [← h]
    abel
end PullbackCoboundary

end Work.ConCohomology
