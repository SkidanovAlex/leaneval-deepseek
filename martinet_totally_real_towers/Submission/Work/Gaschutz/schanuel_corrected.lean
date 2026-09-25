import Mathlib

/-!
# Schanuel's lemma for projective modules

If `f : P →ₗ[R] M` and `g : P' →ₗ[R] M` are surjective linear maps with `P` and `P'`
projective, then `ker f × P' ≃ₗ[R] ker g × P`.

This is Schanuel's lemma.  Proof: form the pullback `N = {(p, p') | f p = g p'}` of `f`
and `g`.  The two projections `N → P` and `N → P'` are surjective, with kernels `ker g`
and `ker f` respectively; each projection splits because its target is projective; hence
`N ≃ ker g × P` and `N ≃ ker f × P'`.
-/

namespace Work.Gaschutz

theorem schanuel_corrected {R M P P' : Type*} [Ring R] [AddCommGroup M] [Module R M]
    [AddCommGroup P] [Module R P] [AddCommGroup P'] [Module R P']
    [Module.Projective R P] [Module.Projective R P']
    (f : P →ₗ[R] M) (hf : Function.Surjective f) (g : P' →ₗ[R] M) (hg : Function.Surjective g) :
    Nonempty ((LinearMap.ker f × P') ≃ₗ[R] (LinearMap.ker g × P)) := by
  -- `h` splits `f` along `g` (using that `P'` is projective), `k` splits `g` along `f`
  -- (using that `P` is projective).
  obtain ⟨h, hh⟩ := Module.projective_lifting_property f g hf
  obtain ⟨k, hk⟩ := Module.projective_lifting_property g f hg
  have hh' : ∀ p' : P', f (h p') = g p' := fun p' => by rw [← LinearMap.comp_apply, hh]
  have hk' : ∀ p : P, g (k p) = f p := fun p => by rw [← LinearMap.comp_apply, hk]
  -- The pullback component maps.
  let A : (LinearMap.ker f) × P' →ₗ[R] P :=
    h.comp (LinearMap.snd R (LinearMap.ker f) P') +
      (LinearMap.ker f).subtype.comp (LinearMap.fst R (LinearMap.ker f) P')
  let B : (LinearMap.ker f) × P' →ₗ[R] P' :=
    LinearMap.snd R (LinearMap.ker f) P' - k.comp A
  have hA : ∀ (x : LinearMap.ker f) (p' : P'), A (x, p') = h p' + (x : P) := fun x p' => rfl
  have hB : ∀ (x : LinearMap.ker f) (p' : P'), B (x, p') = p' - k (h p' + (x : P)) :=
    fun x p' => rfl
  have hBker : ∀ v : (LinearMap.ker f) × P', B v ∈ LinearMap.ker g := by
    rintro ⟨x, p'⟩
    rw [LinearMap.mem_ker, hB, map_sub, hk', map_add, hh']
    have hx : f (x : P) = 0 := LinearMap.mem_ker.mp x.2
    rw [hx, add_zero, sub_self]
  let F : (LinearMap.ker f) × P' →ₗ[R] (LinearMap.ker g) × P :=
    LinearMap.prod (LinearMap.codRestrict (LinearMap.ker g) B hBker) A
  let A' : (LinearMap.ker g) × P →ₗ[R] P' :=
    k.comp (LinearMap.snd R (LinearMap.ker g) P) +
      (LinearMap.ker g).subtype.comp (LinearMap.fst R (LinearMap.ker g) P)
  let B' : (LinearMap.ker g) × P →ₗ[R] P :=
    LinearMap.snd R (LinearMap.ker g) P - h.comp A'
  have hA' : ∀ (y : LinearMap.ker g) (p : P), A' (y, p) = k p + (y : P') := fun y p => rfl
  have hB' : ∀ (y : LinearMap.ker g) (p : P), B' (y, p) = p - h (k p + (y : P')) :=
    fun y p => rfl
  have hB'ker : ∀ v : (LinearMap.ker g) × P, B' v ∈ LinearMap.ker f := by
    rintro ⟨y, p⟩
    rw [LinearMap.mem_ker, hB', map_sub, hh', map_add, hk']
    have hy : g (y : P') = 0 := LinearMap.mem_ker.mp y.2
    rw [hy, add_zero, sub_self]
  let G : (LinearMap.ker g) × P →ₗ[R] (LinearMap.ker f) × P' :=
    LinearMap.prod (LinearMap.codRestrict (LinearMap.ker f) B' hB'ker) A'
  -- Value computations.
  have key1 : ∀ (x : LinearMap.ker f) (p' : P'), k (A (x, p')) + B (x, p') = p' := by
    intro x p'; rw [hA, hB]; abel
  have key2 : ∀ (x : LinearMap.ker f) (p' : P'), A (x, p') - h p' = (x : P) := by
    intro x p'; rw [hA]; abel
  have key3 : ∀ (y : LinearMap.ker g) (p : P), h (A' (y, p)) + B' (y, p) = p := by
    intro y p; rw [hA', hB']; abel
  have key4 : ∀ (y : LinearMap.ker g) (p : P), A' (y, p) - k p = (y : P') := by
    intro y p; rw [hA']; abel
  have hFx : ∀ (x : LinearMap.ker f) (p' : P'),
      F (x, p') = (⟨B (x, p'), hBker (x, p')⟩, A (x, p')) := fun x p' => rfl
  have hGx : ∀ (y : LinearMap.ker g) (p : P),
      G (y, p) = (⟨B' (y, p), hB'ker (y, p)⟩, A' (y, p)) := fun y p => rfl
  -- `F` and `G` are mutually inverse: `F` sends `N ≅ ker f × P'` and `G` realizes
  -- `N ≅ ker g × P`.
  have hGF : G.comp F = LinearMap.id := by
    apply LinearMap.ext
    rintro ⟨x, p'⟩
    rw [LinearMap.comp_apply, LinearMap.id_apply, hFx, hGx]
    apply Prod.ext
    · apply Subtype.ext
      show B' (⟨B (x, p'), hBker (x, p')⟩, A (x, p')) = (x : P)
      rw [hB', key1, key2]
    · show A' (⟨B (x, p'), hBker (x, p')⟩, A (x, p')) = p'
      rw [hA', key1]
  have hFG : F.comp G = LinearMap.id := by
    apply LinearMap.ext
    rintro ⟨y, p⟩
    rw [LinearMap.comp_apply, LinearMap.id_apply, hGx, hFx]
    apply Prod.ext
    · apply Subtype.ext
      show B (⟨B' (y, p), hB'ker (y, p)⟩, A' (y, p)) = (y : P')
      rw [hB, key3, key4]
    · show A (⟨B' (y, p), hB'ker (y, p)⟩, A' (y, p)) = p
      rw [hA, key3]
  exact ⟨LinearEquiv.ofLinearMap F G hFG hGF⟩

end Work.Gaschutz
