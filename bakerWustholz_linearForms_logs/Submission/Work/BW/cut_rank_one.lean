import Mathlib
import Submission.Work.BW.BWGradedBase
import Submission.Work.BW.primLen_ne_top
import Submission.Work.BW.length_quotient_add

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

namespace Work.BW

/-- **A quotient of length one is spanned by any nonzero element.**
Let `A ≤ B` be ideals of a commutative ring `S` and suppose the `S`-module `B ⧸ A` (where `A` is
viewed as a submodule of `B`) has length one. Then there is `x ∈ B`, `x ∉ A`, spanning `B` modulo
`A`: for every `y ∈ B` there is `b : S` with `y - b * x ∈ A`.

The hypothesis makes `B ⧸ A` a simple module; any nonzero element `z = x mod A` generates it
(`IsSimpleModule.span_singleton_eq_top`), so `y mod A = b • z = (b * x) mod A`. -/
lemma exists_smul_sub_mem_of_length_eq_one {S : Type*} [CommRing S] (A B : Ideal S)
    (h : Module.length S (B ⧸ Submodule.comap B.subtype A) = 1) :
    ∃ x ∈ B, x ∉ A ∧ ∀ y ∈ B, ∃ b : S, y - b * x ∈ A := by
  have : IsSimpleModule S (B ⧸ Submodule.comap B.subtype A) := Module.length_eq_one_iff.mp h
  haveI : Nontrivial (B ⧸ Submodule.comap B.subtype A) := IsSimpleModule.nontrivial S _
  obtain ⟨z, hz⟩ := exists_ne (0 : B ⧸ Submodule.comap B.subtype A)
  obtain ⟨w, hw⟩ := Submodule.mkQ_surjective (Submodule.comap B.subtype A) z
  have hz' : Submodule.mkQ (Submodule.comap B.subtype A) w ≠ 0 := by rw [hw]; exact hz
  refine ⟨w.1, w.2, ?_, ?_⟩
  · intro hmem
    apply hz'
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hmem
  · intro y hy
    have hsp : Submodule.span S {z} = ⊤ := IsSimpleModule.span_singleton_eq_top S hz
    have hmem : Submodule.mkQ (Submodule.comap B.subtype A) (⟨y, hy⟩ : B) ∈
        Submodule.span S {z} := by
      rw [hsp]; exact Submodule.mem_top
    rw [Submodule.mem_span_singleton] at hmem
    obtain ⟨b, hb⟩ := hmem
    refine ⟨b, ?_⟩
    have hker : (Submodule.mkQ (Submodule.comap B.subtype A)) ((⟨y, hy⟩ : B) - b • w) = 0 := by
      rw [map_sub, map_smul, hw, hb, sub_self]
    have hmem2 : (⟨y, hy⟩ : B) - b • w ∈ Submodule.comap B.subtype A := by
      rw [← Submodule.ker_mkQ (Submodule.comap B.subtype A)]
      exact LinearMap.mem_ker.mpr hker
    simpa using hmem2

/-- **Descent to `R` of a rank-one generator in the localisation.**
Let `p` be a prime, `I ≤ J` ideals with `J` `p`-primary (`J.radical = p`) or `J = ⊤`. Suppose
`x ∈ J·R_p` spans `J·R_p` modulo `I·R_p`: for every `y ∈ J·R_p` there is `b` in the localisation
with `y - b x ∈ I·R_p`. Then there is `x' ∈ J` such that every `y ∈ J` becomes a multiple of `x'`
modulo `I` after multiplying by an element outside `p`.

Route: write `x = a/u` and use `IsLocalization.surj`; `u ∉ p` shows `a ∈ J` (saturation of a
primary ideal). For `y ∈ J`, the spanning property for `y/1` gives `b`, write `b = c/t`, and
multiply the relation by `u t` and clear denominators with
`IsLocalization.algebraMap_mem_map_algebraMap_iff` to get `m (u t y - c a) ∈ I` with `m ∉ p`. -/
lemma rank_one_descend {R : Type*} [CommRing R] (p : Ideal R) [hp : p.IsPrime]
    (I J : Ideal R)
    (hJ : (J.IsPrimary ∧ J.radical = p) ∨ J = ⊤)
    (x : Localization.AtPrime p)
    (hxJ : x ∈ J.map (algebraMap R (Localization.AtPrime p)))
    (hxspan : ∀ y ∈ J.map (algebraMap R (Localization.AtPrime p)),
      ∃ b : Localization.AtPrime p, y - b * x ∈
        I.map (algebraMap R (Localization.AtPrime p))) :
    ∃ x' ∈ J, ∀ y ∈ J, ∃ d : R, d ∉ p ∧ d * y ∈ I ⊔ Ideal.span {x'} := by
  let S := Localization.AtPrime p
  let f : R →+* S := algebraMap R S
  obtain ⟨⟨a, u⟩, hu⟩ := IsLocalization.surj p.primeCompl x
  have hfa : f a ∈ J.map f := by
    rw [← hu]
    exact Ideal.mul_mem_right _ _ hxJ
  obtain ⟨m, hm, hma⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff p.primeCompl S J a).mp hfa
  have hm_notin : m ∉ p := Ideal.mem_primeCompl_iff.mp hm
  have haJ : a ∈ J := by
    rcases hJ with ⟨hprim, hrad⟩ | htop
    · rcases hprim.mem_or_mem (show m • a ∈ (J : Submodule R R) from by simpa using hma) with
        h | h
      · exact h
      · rw [Submodule.colon_univ, hrad] at h
        exact absurd h hm_notin
    · rw [htop]; exact Submodule.mem_top
  refine ⟨a, haJ, ?_⟩
  intro y hy
  have hy' : f y ∈ J.map f := Ideal.mem_map_of_mem f hy
  obtain ⟨b, hb⟩ := hxspan (f y) hy'
  obtain ⟨⟨c, t⟩, ht⟩ := IsLocalization.surj p.primeCompl b
  have hmem : f (↑u * ↑t * y - c * a) ∈ I.map f := by
    have h1 : f ↑t * (f y - b * x) ∈ I.map f := Ideal.mul_mem_left _ _ hb
    have h2 : f ↑u * (f ↑t * (f y - b * x)) ∈ I.map f := Ideal.mul_mem_left _ _ h1
    have heq : f ↑u * (f ↑t * (f y - b * x)) = f (↑u * ↑t * y - c * a) := by
      simp only [map_sub, map_mul]
      rw [← hu, ← ht]
      ring
    rwa [heq] at h2
  obtain ⟨m', hm', hm'i⟩ :=
    (IsLocalization.algebraMap_mem_map_algebraMap_iff p.primeCompl S I
      (↑u * ↑t * y - c * a)).mp hmem
  have hm'_notin : m' ∉ p := Ideal.mem_primeCompl_iff.mp hm'
  have ht_notin : (t : R) ∉ p := Ideal.mem_primeCompl_iff.mp t.2
  have hu_notin : (u : R) ∉ p := Ideal.mem_primeCompl_iff.mp u.2
  refine ⟨m' * ↑u * ↑t, ?_, ?_⟩
  · intro hcon
    rcases hp.mem_or_mem hcon with h | h
    · rcases hp.mem_or_mem h with h1 | h1
      · exact hm'_notin h1
      · exact hu_notin h1
    · exact ht_notin h
  · have hz : (m' * ↑u * ↑t) * y = m' * (↑u * ↑t * y - c * a) + a * (m' * c) := by ring
    rw [hz]
    refine Submodule.mem_sup.mpr ⟨m' * (↑u * ↑t * y - c * a), hm'i, a * (m' * c), ?_, ?_⟩
    · exact Ideal.mul_mem_right (m' * c) _ (Ideal.mem_span_singleton_self a)
    · ring

/-- **The rank-one step, saturated form.**

Let `R` be Noetherian, `p` a prime, `I ≤ J` ideals, `J` a `p`-primary ideal with radical `p` (or
`J = ⊤`), and suppose the `p`-local length drops by exactly one from `I` to `J`
(`locLenAt p hp I = locLenAt p hp J + 1`). Then there is `x ∈ J` such that every `y ∈ J` becomes a
multiple of `x` modulo `I` after multiplying by an element outside `p`:
`∃ d ∉ p, d * y ∈ I ⊔ (x)`.

Route (write `S := Localization.AtPrime p = R_p`, `f := algebraMap R S`).

* Case `J = ⊤`: take `x = 1`, `d = 1` (`I ⊔ (1) = ⊤`).
* Case `J` `p`-primary with `J.radical = p`: then `p` is a minimal prime of `J` (`Ideal.radical J =
  p`, `Ideal.radical_minimalPrimes`, `Ideal.minimalPrimes_eq_subsingleton_self`), so
  `locLenAt p hp J ≠ ⊤` (`Work.BW.primLen_ne_top_aux` in `Submission.Work.BW.primLen_ne_top`).
  Since `I ≤ J`, the sequence `0 → J·S/I·S → S/I·S → S/J·S → 0` is exact, and
  `Module.length_eq_add_of_exact` together with `hrank` gives
  `ℓ(J·S/I·S) + ℓ(S/J·S) = ℓ(S/J·S) + 1`; with `ℓ(S/J·S) ≠ ⊤` cancellation in `ℕ∞` gives
  `ℓ(J·S/I·S) = 1`. Hence `J·S/I·S` is simple, i.e. the residue field `S/p·S`; in particular it is
  nonzero, so pick `x ∈ J` with `x ∉ I·S` (exists because otherwise `J·S = I·S`), and then
  `J·S = I·S + S·x` (a simple module is generated by any nonzero element: use
  `IsSimpleModule.span_singleton_eq_top`).
* Finally let `y ∈ J`; write `y ∈ J·S = I·S + S·x` as `y = i/s + (a/u)·x` with `i ∈ I`, `a ∈ R`
  and `s, u ∉ p`, and multiply by `d := s·u ∉ p` (as `p` is prime):
  `d·y = u·i + (s·a)·x ∈ I ⊔ (x)`. -/
theorem cut_rank_one {R : Type*} [CommRing R] [IsNoetherianRing R]
    (p : Ideal R) (hp : p.IsPrime) (I J : Ideal R) (hIJ : I ≤ J)
    (hJ : (J.IsPrimary ∧ J.radical = p) ∨ J = ⊤)
    (hrank : Work.BW.locLenAt p hp I = Work.BW.locLenAt p hp J + 1) :
    ∃ x ∈ J, ∀ y ∈ J, ∃ d : R, d ∉ p ∧ d * y ∈ I ⊔ Ideal.span {x} := by
  letI : p.IsPrime := hp
  let S := Localization.AtPrime p
  let f : R →+* S := algebraMap R S
  let IS : Submodule S S := I.map f
  let JS : Submodule S S := J.map f
  have hIJ' : IS ≤ JS := Ideal.map_mono (f := f) hIJ
  -- The localised quotient `S ⧸ J·S` has finite length.
  have hJlen : Module.length S (S ⧸ JS) ≠ ⊤ := by
    rcases hJ with ⟨hprim, hrad⟩ | htop
    · have hpmin : p ∈ J.minimalPrimes := by
        rw [← Ideal.radical_minimalPrimes (I := J), hrad,
          Ideal.minimalPrimes_eq_subsingleton_self]
        exact Set.mem_singleton p
      simpa only [S, f, JS] using primLen_ne_top_aux J p hpmin
    · have hJSt : JS = ⊤ := by simp only [JS, htop, Ideal.map_top]
      rw [hJSt]
      have : Module.length S (S ⧸ (⊤ : Submodule S S)) = 0 := Module.length_eq_zero
      rw [this]; exact ENat.zero_ne_top
  -- Additivity of length along `0 → J·S/I·S → S/I·S → S/J·S → 0`.
  have hadd : Module.length S (S ⧸ IS) =
      Module.length S (S ⧸ JS) + Module.length S (JS ⧸ IS.comap JS.subtype) :=
    length_quotient_add IS JS hIJ'
  -- Rewrite the hypothesis in terms of the localised lengths.
  have hrank' : Module.length S (S ⧸ IS) = Module.length S (S ⧸ JS) + 1 := by
    have h1 : Work.BW.locLenAt p hp I = Module.length S (S ⧸ IS) := rfl
    have h2 : Work.BW.locLenAt p hp J = Module.length S (S ⧸ JS) := rfl
    rw [h1, h2] at hrank
    exact hrank
  -- Cancellation in `ℕ∞`: the localised step has length exactly one.
  have hlen : Module.length S (JS ⧸ IS.comap JS.subtype) = 1 := by
    refine (add_right_inj_of_ne_top hJlen).mp ?_
    rw [← hadd, hrank']
  -- The step `J·S/I·S` is a length-one module, hence generated by any nonzero element.
  obtain ⟨x, hxJ, -, hxspan⟩ :=
    exists_smul_sub_mem_of_length_eq_one IS JS hlen
  exact rank_one_descend p I J hJ x hxJ hxspan

end Work.BW
