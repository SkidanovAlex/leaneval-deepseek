import Mathlib
import Submission.Work.SSGRoute.CycLevel.GrunwaldImports
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.CycLevel

/-- **Index of the preimage of a prime-index subgroup under the one-place map.**

Let `V ≤ C_k` have index `q` (`q` prime), and let `x ∈ k_{v₀}ˣ` have `onePlace`-class outside `V`.
Then the preimage of `V` under the composite
`k_{v₀}ˣ → 𝕀_k → C_k` has index `q`.

Indeed `[(k_{v₀}ˣ) : f⁻¹V] = [f(A) : f(A) ∩ V]` divides `[C_k : V] = q`, and it is `> 1` because
`f(x) ∉ V`; as `q` is prime the index is `q`.  (This is the index computation used to identify the
local norm index of a level whose norm class subgroup is `V`.) -/
theorem index_comap_onePlace_eq (k : Type) [Field k] [NumberField k]
    (v₀ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (q : ℕ) (hq : q.Prime)
    (V : Subgroup (NK.GlobalCFT.IdeleClassGroup k)) (hV : V.index = q)
    (x : (v₀.adicCompletion k)ˣ)
    (hx : NK.GlobalCFT.IdeleClassGroup.mk k
        (NK.HassePrinciple.onePlace (NK.GlobalCFT.Place.ofFinite v₀) x) ∉ V) :
    (Subgroup.comap
      ((NK.GlobalCFT.IdeleClassGroup.mk k).comp
        (NK.CFTLib.IdeleHasse.onePlaceHom (NK.GlobalCFT.Place.ofFinite v₀))) V).index = q := by
  -- Abbreviate the one-place map `k_{v₀}ˣ → 𝕀_k → C_k` and the preimage of `V`.
  set f : (v₀.adicCompletion k)ˣ →* NK.GlobalCFT.IdeleClassGroup k :=
    (NK.GlobalCFT.IdeleClassGroup.mk k).comp
      (NK.CFTLib.IdeleHasse.onePlaceHom (NK.GlobalCFT.Place.ofFinite v₀)) with hf
  set W : Subgroup (v₀.adicCompletion k)ˣ := Subgroup.comap f V with hW
  -- `x` lies outside the preimage, since its `f`-image lies outside `V`.
  have hxW : x ∉ W := by
    rw [hW, Subgroup.mem_comap, hf]
    exact hx
  -- `[A : W] = [C_k : V].relIndex f.range` divides `[C_k : V] = q`, because `V` is normal
  -- (`C_k` is abelian) so `relIndex_dvd_index_of_normal` applies.
  have hdiv : W.index ∣ q := by
    rw [← hV]
    calc W.index = V.relIndex f.range := by rw [hW]; exact Subgroup.index_comap V f
      _ ∣ V.index := Subgroup.relIndex_dvd_index_of_normal V f.range
  -- The index is not `1`: otherwise `W = ⊤`, contradicting `x ∉ W`.
  have hone : W.index ≠ 1 := by
    intro h
    rw [Subgroup.index_eq_one] at h
    exact hxW (by rw [h]; exact Subgroup.mem_top x)
  -- A divisor of the prime `q` is `1` or `q`; the first case is excluded.
  rcases hq.eq_one_or_self_of_dvd W.index hdiv with h | h
  · exact absurd h hone
  · exact h

end Work.SSGRoute.CycLevel
