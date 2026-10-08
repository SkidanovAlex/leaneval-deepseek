import Mathlib
import Submission.Work.FeitSibley.Coherence.Vocab
import Submission.Work.Frobenius.Nilpotent.Kernel
import Submission.Work.ThompsonFrobenius.Main
import Submission.Work.GlaubermanZJ.Main
import Submission.Work.ThmF.ChV12.glaubermanZJ_free

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Q₁` is nilpotent when `D ≠ ⊥`

Peterfalvi II, Appendice XII, p. 288: `H = Q ⋊ D` with `Q = S × Q₁`, and `D` acts
fixed-point-freely on `Q₁`.  As soon as `D ≠ 1`, `Q₁ ≠ 1` carries a fixed-point-free
automorphism group of coprime order, so `Q₁` is nilpotent (`Q₁ D` is a Frobenius group with
kernel `Q₁`, and Thompson's theorem says that Frobenius kernels are nilpotent).

The formalisation takes a nontrivial element `d ∈ D` of prime order `p` (Cauchy; this exists
because `|D|` is odd, hence `> 1` once `D ≠ ⊥`), views conjugation by `d` as an automorphism
`α` of `↥Q₁` (it preserves `Q₁` because `D ≤ H ≤ N_G(Q₁)`), and applies Thompson's theorem in
the form `Work.ThompsonFrobenius.isNilpotent_of_fpf_pow`: `α` is fixed-point-free (`D_fpf_Q1`)
and `α ^ p = 1`.

Thompson's theorem is applied with the Glauberman `ZJ`-theorem, which is available
unconditionally in this workspace as `Work.ThmF.ChV12.glaubermanZJ_free` (the Feit–Thompson
hypothesis carried by `Work.GlaubermanZJ.GlaubermanZJ` is vestigial).
-/

namespace Work.FeitSibley.Coherence

noncomputable section

open Classical

variable {G : Type} [Group G] [Fintype G]

/-- Conjugation by an element `d` of the normaliser of `Q₁`, as an automorphism of `↥Q₁`. -/
def conjAut (h : Work.FeitSibley.FSData G) (d : G)
    (hd : d ∈ Subgroup.normalizer (h.Q1 : Set G)) : MulAut ↥h.Q1 where
  toFun x := ⟨d * (x : G) * d⁻¹, (Subgroup.mem_normalizer_iff.mp hd (x : G)).mp x.2⟩
  invFun x := ⟨d⁻¹ * (x : G) * d, by
    have h := (Subgroup.mem_normalizer_iff.mp (inv_mem hd) (x : G)).mp x.2
    simpa using h⟩
  left_inv x := Subtype.ext (by simp [mul_assoc])
  right_inv x := Subtype.ext (by simp [mul_assoc])
  map_mul' x y := Subtype.ext (by simp [mul_assoc])

@[simp]
theorem conjAut_apply (h : Work.FeitSibley.FSData G) (d : G)
    (hd : d ∈ Subgroup.normalizer (h.Q1 : Set G)) (x : ↥h.Q1) :
    ((conjAut h d hd x : ↥h.Q1) : G) = d * (x : G) * d⁻¹ := rfl

/-- The conjugation action of `N_G(Q₁)` on `Q₁`. -/
def conjHom (h : Work.FeitSibley.FSData G) :
    ↥(Subgroup.normalizer (h.Q1 : Set G)) →* MulAut ↥h.Q1 where
  toFun d := conjAut h (d : G) d.2
  map_one' := by
    ext x
    simp [conjAut]
  map_mul' a b := by
    ext x
    simp only [conjAut_apply, MulAut.mul_apply, Subgroup.coe_mul]
    group

@[simp]
theorem conjHom_apply (h : Work.FeitSibley.FSData G)
    (d : ↥(Subgroup.normalizer (h.Q1 : Set G))) (x : ↥h.Q1) :
    ((conjHom h d x : ↥h.Q1) : G) = (d : G) * (x : G) * (d : G)⁻¹ := rfl

theorem Q1_isNilpotent_of_D_ne_bot {G : Type} [Group G] [Fintype G]
    (h : Work.FeitSibley.FSData G) (hD : h.D ≠ ⊥) :
    Group.IsNilpotent ↥h.Q1 := by
  classical
  -- Thompson's theorem, with the Glauberman `ZJ`-theorem taken from the Feit–Thompson-free
  -- version available in the workspace.
  have hZJ : Submission.Blueprint.GlaubermanZJProp := Work.ThmF.ChV12.glaubermanZJ_free
  -- A nontrivial element `d` of `D` of prime order `p` (Cauchy's theorem).
  have hD1 : 1 < Nat.card h.D := (Subgroup.one_lt_card_iff_ne_bot h.D).mpr hD
  obtain ⟨p, hp, hpdvd⟩ :=
    Nat.exists_prime_and_dvd (Nat.one_lt_iff_ne_zero_and_ne_one.mp hD1).2
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hpdvd' : p ∣ Fintype.card ↥h.D := by
    rwa [Nat.card_eq_fintype_card] at hpdvd
  obtain ⟨d, hdord⟩ := exists_prime_orderOf_dvd_card (G := ↥h.D) p hpdvd'
  have hdne : (d : G) ≠ 1 := by
    intro hc
    have hd1 : d = 1 := Subtype.ext (by simpa using hc)
    exact hp.ne_one (by rw [← hdord, hd1, orderOf_one])
  have hdN : (d : G) ∈ Subgroup.normalizer (h.Q1 : Set G) :=
    h.Q1_normal_in_H (h.D_le_H d.2)
  -- Conjugation by `d`, as an automorphism of `Q₁`, with `α ^ p = 1`.
  let g : ↥(Subgroup.normalizer (h.Q1 : Set G)) := ⟨(d : G), hdN⟩
  let α : MulAut ↥h.Q1 := conjHom h g
  have hgp : g ^ p = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    change (d : G) ^ p = 1
    rw [← hdord, ← Subgroup.orderOf_coe d, pow_orderOf_eq_one]
  have hαp : α ^ p = 1 := by
    show (conjHom h g) ^ p = 1
    rw [← map_pow, hgp, map_one]
  -- `α` is fixed-point-free, by `D_fpf_Q1`.
  have hαfpf : Work.NPC.Fpf.IsFpf α := by
    intro x hx
    have hxg : (d : G) * (x : G) * (d : G)⁻¹ = (x : G) := by
      have h := congrArg (fun y : ↥h.Q1 => (y : G)) hx
      simpa [α, conjHom_apply, g] using h
    have hx1 : (x : G) = 1 :=
      h.D_fpf_Q1 (d : G) d.2 hdne (x : G) x.2 hxg
    exact Subtype.ext (by simpa using hx1)
  exact Work.ThompsonFrobenius.isNilpotent_of_fpf_pow hZJ (Nat.card ↥h.Q1) ↥h.Q1 rfl α p hp
    hαp hαfpf

end

end Work.FeitSibley.Coherence
