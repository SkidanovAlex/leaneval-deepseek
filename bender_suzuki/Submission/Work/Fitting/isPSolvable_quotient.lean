import Mathlib
import Submission.Work.Fitting.Defs
import Submission.Work.Fitting.piCore_isPiNat

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.Fitting.isPSolvable_quotient`

`p`-solvability passes to quotients: if `G` is a `p`-solvable finite group and `N ◁ G`, then
`G ⧸ N` is `p`-solvable.

The upper `p`-series `1 = O_0 ≤ O_{p'}(G) ≤ O_{p',p}(G) ≤ ...` of `G` is compatible with
surjective homomorphisms: the image of the `n`-th term of the series of `G` is contained in
the `n`-th term of the series of the target.  Since `IsPSolvable p G` says that some term of
the series is `⊤`, its image is `⊤`, so the corresponding term of `G ⧸ N` is `⊤` as well.

The key local input is that `O_π` is carried into `O_π` by a surjective homomorphism: the
image of `O_π(G)` is normal and its order divides `|O_π(G)|`.
-/

noncomputable section

open Classical

namespace Work.Fitting

/-- A surjective homomorphism carries the `π`-core of its source into the `π`-core of its
target: the image of `O_π(G)` is normal and has order dividing `|O_π(G)|`, hence is a normal
`π`-subgroup of the target. -/
theorem piCore_map_le {π : ℕ → Prop} {G H : Type*} [Group G] [Group H] [Finite G]
    (f : G →* H) (hf : Function.Surjective f) :
    (piCore π G).map f ≤ piCore π H := by
  refine le_piCore (Subgroup.Normal.map (inferInstance : (piCore π G).Normal) f hf) ?_
  exact isPiNat_of_dvd (Subgroup.card_map_dvd (piCore π G) f) (piCore_isPiNat G π)

/-- A surjective homomorphism `f : G →* H` of finite groups carries the `n`-th term of the
upper `p`-series of `G` into the `n`-th term of the upper `p`-series of `H`. -/
theorem pCoreSeries_map_le (p : ℕ) (G H : Type*) [Group G] [Group H] [Finite G] [Finite H]
    (f : G →* H) (hf : Function.Surjective f) (n : ℕ) :
    (pCoreSeries p G n).map f ≤ pCoreSeries p H n := by
  induction n with
  | zero => rw [pCoreSeries_zero, Subgroup.map_bot]; exact bot_le
  | succ n ih =>
    rw [pCoreSeries_succ, pCoreSeries_succ]
    haveI hMn : (pCoreSeries p G n).Normal := pCoreSeries_normal p G n
    haveI hKn : (pCoreSeries p H n).Normal := pCoreSeries_normal p H n
    -- The induction hypothesis says `O_n(G) ≤ f⁻¹(O_n(H))`.
    have hMK : pCoreSeries p G n ≤ (pCoreSeries p H n).comap f :=
      Subgroup.map_le_iff_le_comap.mp ih
    -- The induced surjection `G/O_n(G) → H/O_n(H)`.
    have hQsurj : Function.Surjective
        (QuotientGroup.map (pCoreSeries p G n) (pCoreSeries p H n) f hMK) :=
      QuotientGroup.map_surjective_of_surjective _ _ f
        ((QuotientGroup.mk_surjective (s := pCoreSeries p H n)).comp hf) hMK
    have hcore : piCore (fun q => if Even n then q ≠ p else q = p) (G ⧸ pCoreSeries p G n) ≤
        (piCore (fun q => if Even n then q ≠ p else q = p) (H ⧸ pCoreSeries p H n)).comap
          (QuotientGroup.map (pCoreSeries p G n) (pCoreSeries p H n) f hMK) :=
      Subgroup.map_le_iff_le_comap.mp
        (piCore_map_le (π := fun q => if Even n then q ≠ p else q = p) _ hQsurj)
    intro y hy
    rw [Subgroup.mem_map] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [Subgroup.mem_comap] at hx ⊢
    have h3 := Subgroup.mem_comap.mp (hcore hx)
    rw [QuotientGroup.map_mk' (pCoreSeries p G n) (pCoreSeries p H n) f hMK x] at h3
    exact h3

theorem isPSolvable_quotient (p : ℕ) (G : Type*) [Group G] [Finite G] (N : Subgroup G) [N.Normal]
    [Work.Fitting.IsPSolvable p G] : Work.Fitting.IsPSolvable p (G ⧸ N) := by
  obtain ⟨n, hn⟩ := (inferInstance : IsPSolvable p G).out
  refine ⟨n, ?_⟩
  have h := pCoreSeries_map_le p G (G ⧸ N) (QuotientGroup.mk' N)
    (QuotientGroup.mk'_surjective N) n
  rw [hn, Subgroup.map_top_of_surjective (QuotientGroup.mk' N)
    (QuotientGroup.mk'_surjective N)] at h
  exact top_le_iff.mp h

end Work.Fitting
