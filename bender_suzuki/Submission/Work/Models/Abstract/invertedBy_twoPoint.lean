import Mathlib
import Submission.Work.Models.Port.BenderSetup
import Submission.Work.Models.Basic
import Submission.Work.Models.Abstract.inf_conj_w
import Submission.Work.Models.Abstract.eq_mul_w_of_mem_normalizer
import Submission.Work.Models.Abstract.invertedBy_conj_eq
import Submission.Work.Models.Port.Commons.GroupTheory.Subgroup.normalizer_map_mulAut_conj

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Models.Abstract.invertedBy_twoPoint`

For a Bender pair `P` (a split rank-one `(B,N)`-pair of characteristic two: `B = U ⋊ T`, `w` a
Weyl element), with the torus `T` abelian and `w² = 1`, and for an involution `t ∉ B`:

* the two-point stabiliser `D = B ⊓ B^t` is a `B`-conjugate of the torus `T`, and
* the set of elements of `D` inverted by `t`, i.e. `J(D,t) = invertedBy D t`, is the
  corresponding conjugate of `J(T,w) = invertedBy T w`.

Both halves come from the Bruhat decomposition: `t ∉ B` gives `t = b * w * c` with `b, c ∈ B`
(`BenderPair.bruhat`), and then a direct computation gives

`D = B ⊓ B^t = conj b (B ⊓ conj w B) = conj b T`,

the last step being `inf_conj_w`.

For the second half put `s = b⁻¹ * t * b = w * c * b`.  Since `t² = 1`, conjugation by `t`
maps `B^t` to `B`, so `t` normalises `D`; conjugating by `b` this says `s ∈ N(T)`, and
`s ∉ B` (else `t = b s b⁻¹ ∈ B`) forces `s = d * w` with `d ∈ T`
(`eq_mul_w_of_mem_normalizer`).  Multiplying the inverting element by `d` is invisible inside
the abelian `T`, so `invertedBy T s = invertedBy T w`, and transporting along the conjugation
by `b` (`invertedBy_conj_eq`) gives the statement.
-/

set_option autoImplicit false

namespace Work.Models.Abstract

/-- Multiplying the inverting element by an element of the abelian subgroup `T` (which is
translated inside `T`) does not change `invertedBy T ·`. -/
theorem invertedBy_mul_mem_abelian_aux {G : Type*} [Group G] {T : Subgroup G} {w d : G}
    (hTab : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x) (hd : d ∈ T)
    (hwT : ∀ y ∈ T, w * y * w⁻¹ ∈ T) :
    Submission.Blueprint.invertedBy T (d * w) = Submission.Blueprint.invertedBy T w := by
  have hconj : ∀ y ∈ T, (d * w) * y * (d * w)⁻¹ = w * y * w⁻¹ := fun y hy => by
    have hcomm : d * (w * y * w⁻¹) = (w * y * w⁻¹) * d := hTab d hd _ (hwT y hy)
    calc (d * w) * y * (d * w)⁻¹ = d * (w * y * w⁻¹) * d⁻¹ := by group
      _ = w * y * w⁻¹ := by rw [hcomm]; group
  ext x
  rw [Work.Models.mem_invertedBy_iff, Work.Models.mem_invertedBy_iff]
  constructor
  · rintro ⟨hxT, hx⟩
    exact ⟨hxT, by rw [hconj x hxT] at hx; exact hx⟩
  · rintro ⟨hxT, hx⟩
    exact ⟨hxT, by rw [hconj x hxT]; exact hx⟩

/-- If `t = b * w * c` with `b, c ∈ B` then the two-point stabiliser `B ⊓ B^t` is the
`b`-conjugate of `T = B ⊓ B^w`. -/
theorem twoPoint_eq_conj_of_bruhat_aux {G : Type*} [Group G] [Finite G]
    (P : Submission.BenderPair G) {t b c : G} (hb : b ∈ P.B) (hc : c ∈ P.B)
    (htbc : t = b * P.w * c) :
    Submission.Blueprint.twoPoint P.B t = Submission.Blueprint.conj b P.T := by
  ext x
  rw [Work.Models.mem_twoPoint_iff, Work.Models.mem_conj_iff, ← inf_conj_w P, Subgroup.mem_inf,
    Work.Models.mem_conj_iff]
  -- `(x ∈ B ∧ t⁻¹xt ∈ B) ↔ (b⁻¹xb ∈ B ∧ w⁻¹(b⁻¹xb)w ∈ B)`
  have hkey : P.w⁻¹ * (b⁻¹ * x * b) * P.w = c * (t⁻¹ * x * t) * c⁻¹ := by
    rw [htbc]; group
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨P.B.mul_mem (P.B.mul_mem (P.B.inv_mem hb) h1) hb,
      by rw [hkey]; exact P.B.mul_mem (P.B.mul_mem hc h2) (P.B.inv_mem hc)⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · have : x = b * (b⁻¹ * x * b) * b⁻¹ := by group
      rw [this]
      exact P.B.mul_mem (P.B.mul_mem hb h1) (P.B.inv_mem hb)
    · have : t⁻¹ * x * t = c⁻¹ * (P.w⁻¹ * (b⁻¹ * x * b) * P.w) * c := by
        rw [hkey]; group
      rw [this]
      exact P.B.mul_mem (P.B.mul_mem (P.B.inv_mem hc) h2) hc

theorem invertedBy_twoPoint {G : Type*} [Group G] [Finite G] (P : Submission.BenderPair G)
    (hTab : ∀ x ∈ P.T, ∀ y ∈ P.T, x * y = y * x) (hww : P.w * P.w = 1)
    {t : G} (ht2 : orderOf t = 2) (ht : t ∉ P.B) :
    ∃ b ∈ P.B, Submission.Blueprint.twoPoint P.B t = Submission.Blueprint.conj b P.T ∧
      Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint P.B t) t
        = (fun x => b * x * b⁻¹) '' Submission.Blueprint.invertedBy P.T P.w := by
  -- Bruhat decomposition of `t ∉ B`.
  obtain ⟨b, c, htbc⟩ : ∃ b c : ↥P.B, t = (b : G) * P.w * (c : G) := by
    rcases P.bruhat t with h | h
    · exact absurd h ht
    · exact h
  have hbB : (b : G) ∈ P.B := b.2
  have hD : Submission.Blueprint.twoPoint P.B t = Submission.Blueprint.conj (b : G) P.T :=
    twoPoint_eq_conj_of_bruhat_aux P (t := t) (b := (b : G)) (c := (c : G)) b.2 c.2 htbc
  -- `t` is an involution.
  have hsq : t * t = 1 := by
    have h := pow_orderOf_eq_one t
    rw [ht2] at h
    simpa [pow_two] using h
  -- `t` normalises its two-point stabiliser `D = B ⊓ B^t`: conjugation by `t` exchanges the
  -- two factors of the intersection.
  have htN : t ∈ Subgroup.normalizer (Submission.Blueprint.twoPoint P.B t : Set G) := by
    have hinvt : t⁻¹ = t := inv_eq_of_mul_eq_one_right hsq
    have hkey : ∀ x : G, t * (t * x * t) * t = x := fun x => by
      calc t * (t * x * t) * t = (t * t) * x * (t * t) := by group
        _ = x := by rw [hsq, one_mul, mul_one]
    rw [Subgroup.mem_normalizer_iff]
    intro x
    show x ∈ P.B ⊓ Submission.Blueprint.conj t P.B
        ↔ t * x * t⁻¹ ∈ P.B ⊓ Submission.Blueprint.conj t P.B
    rw [Subgroup.mem_inf, Subgroup.mem_inf, Work.Models.mem_conj_iff, Work.Models.mem_conj_iff,
      hinvt]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h2, by rw [hkey x]; exact h1⟩
    · rintro ⟨h1, h2⟩
      exact ⟨by rw [← hkey x]; exact h2, h1⟩
  -- Hence `s = b⁻¹ * t * b ∈ N(T)`.
  have hsN : (b : G)⁻¹ * t * (b : G) ∈ Subgroup.normalizer (P.T : Set G) := by
    have h1 : t ∈ (Subgroup.normalizer (P.T : Set G)).map (MulAut.conj (b : G)).toMonoidHom := by
      have hh : t ∈ Subgroup.normalizer (Submission.Blueprint.conj (b : G) P.T : Set G) :=
        hD ▸ htN
      have hh' : t ∈ Subgroup.normalizer ((P.T.map (MulAut.conj (b : G)).toMonoidHom) : Set G) :=
        hh
      rwa [Commons.GroupTheory.Subgroup.normalizer_map_mulAut_conj] at hh'
    rw [Subgroup.mem_map] at h1
    obtain ⟨x, hx, hxt⟩ := h1
    have hx_eq : x = (b : G)⁻¹ * t * (b : G) := by
      rw [← hxt]
      change x = (b : G)⁻¹ * ((b : G) * x * (b : G)⁻¹) * (b : G)
      group
    rwa [hx_eq] at hx
  -- ... and `s ∉ B`, since otherwise `t = b * s * b⁻¹ ∈ B`.
  have hsB : (b : G)⁻¹ * t * (b : G) ∉ P.B := by
    intro hmem
    refine ht ?_
    have : t = (b : G) * ((b : G)⁻¹ * t * (b : G)) * (b : G)⁻¹ := by group
    rw [this]
    exact P.B.mul_mem (P.B.mul_mem hbB hmem) (P.B.inv_mem hbB)
  refine ⟨(b : G), hbB, hD, ?_⟩
  -- `N(T) \ B = T * w` (because `s ∈ N(T) = T ⊔ ⟨w⟩` and `s ∉ B ⊆` the `T`-part).
  obtain ⟨d, hd, hsd⟩ := eq_mul_w_of_mem_normalizer P hww hsN hsB
  rw [hD, invertedBy_conj_eq P.T (b : G) t, hsd,
    invertedBy_mul_mem_abelian_aux hTab hd
      (fun y hy => (Subgroup.mem_normalizer_iff.mp P.hwT y).mp hy)]

end Work.Models.Abstract
