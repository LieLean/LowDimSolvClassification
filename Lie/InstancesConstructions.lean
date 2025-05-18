import Mathlib.Algebra.Lie.Basic
import Mathlib.Algebra.Lie.Abelian
import Mathlib.LinearAlgebra.AffineSpace.AffineMap
import Lie.Semidirect
import Mathlib.Algebra.Lie.DirectSum
import Lie.GeneralResults
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Trace


open Module
open Submodule

namespace LieAlgebra

section mkAbelian

/-- The abelian Lie algebra constructed from a vector space by setting the bracket to zero. -/
def mkAbelian (K : Type*) [CommRing K] (V : Type*) [AddCommGroup V] [Module K V] := V

variable (K : Type*) [CommRing K] (V : Type*) [AddCommGroup V] [Module K V]

instance [Module K V] : Bracket (mkAbelian K V) (mkAbelian K V) := {
  bracket := fun _ _ ↦ (0 : V)
}

instance [Module K V] : LieRing (mkAbelian K V) := {
  (inferInstance : AddCommGroup V) with
  add_lie := fun _ _ _ ↦ by simp only [mkAbelian, Bracket.bracket, add_zero]
  lie_add := fun _ _ _ ↦ by simp only [mkAbelian, Bracket.bracket, add_zero]
  lie_self := fun _ ↦ by simp only [Bracket.bracket]
  leibniz_lie := fun _ _ _ ↦ by simp only [mkAbelian, Bracket.bracket, add_zero]
}

instance [Module K V] : LieAlgebra K (mkAbelian K V) := {
  (inferInstance : Module K V) with
  lie_smul := fun _ _ _ ↦ by simp only [mkAbelian, Bracket.bracket, smul_zero]
}

instance [Module K V] : IsLieAbelian (mkAbelian K V) :=
  ⟨fun _ _ ↦ by simp only [Bracket.bracket]⟩

end mkAbelian

section abelianDerivation

def Abelian.DerivationOfLinearMap' {K : Type*} [CommRing K] {L : Type*} [LieRing L] [LieAlgebra K L] [IsLieAbelian L] (f : End K L) :
    LieDerivation K L L := {
  toLinearMap := f,
  leibniz' := by
    intro x y
    simp only [trivial_lie_zero, map_zero, sub_self]
}

/-- If `L` is an abelian Lie algebra, any linear endomorphism of L is also a derivation of L.-/
def Abelian.DerivationOfLinearMap (K L : Type*) [CommRing K] [LieRing L] [LieAlgebra K L] [IsLieAbelian L] :
    End K L ≃ₗ⁅K⁆ LieDerivation K L L := {
  toFun := Abelian.DerivationOfLinearMap',
  map_add' := by
    intro f g
    ext x
    unfold Abelian.DerivationOfLinearMap'
    simp only [LieDerivation.mk_coe, LinearMap.add_apply, LieDerivation.coe_add, Pi.add_apply]
  map_smul' := by
    intro a f
    ext x
    unfold Abelian.DerivationOfLinearMap'
    simp only [LieDerivation.mk_coe, LinearMap.smul_apply, RingHom.id_apply, LieDerivation.coe_smul,
      Pi.smul_apply]
  map_lie' := by
    intro f g
    ext x
    unfold Abelian.DerivationOfLinearMap'
    simp only [LieDerivation.mk_coe, LieHom.lie_apply, End.lie_apply, LieDerivation.lie_apply]
  invFun := LieDerivation.toLinearMap
  left_inv := by
    intro f
    rfl
  right_inv := by
    intro f
    rfl
}

@[simp]
theorem Abelian.DerivationCoeLinearMap {K : Type*} [CommRing K] {L : Type*} [LieRing L] [LieAlgebra K L] [IsLieAbelian L] (f : L →ₗ[K] L) :
    (Abelian.DerivationOfLinearMap K L f).toLinearMap = f := rfl

@[simp]
theorem Abelian.DerivationCoeFun {K : Type*} [CommRing K] {L : Type*} [LieRing L] [LieAlgebra K L] [IsLieAbelian L] (f : L →ₗ[K] L) :
    ⇑(Abelian.DerivationOfLinearMap K L f) = ⇑f := rfl

@[simp]
theorem Abelian.DerivationCoeFun' {K : Type*} [CommRing K] {L : Type*} [LieRing L] [LieAlgebra K L] [IsLieAbelian L] (f : L →ₗ[K] L) :
    ⇑((Abelian.DerivationOfLinearMap K L).toLieHom f) = ⇑f := rfl

end abelianDerivation

section liealgofaffineequiv

variable (K : Type*) [CommRing K] (V : Type*) [AddCommGroup V] [Module K V]

def ofAffineEquivAux := (Abelian.DerivationOfLinearMap K (mkAbelian K V)).toLieHom

/-- The Lie algebra of the general affine group on a vector space `V`,
    constructed as semidirect product of `V →ₗ[K] V` with the abelian Lie algebra `V`. -/
abbrev OfAffineEquiv [Module K V] := End K V ⋉[ofAffineEquivAux K V] mkAbelian K V
-- one could also define it as V →ᵃ[K] V, but the Lie bracket is not defined using function composition (not left-distributive).

@[inherit_doc]
notation "𝔞𝔣𝔣" => OfAffineEquiv

end liealgofaffineequiv

section liealghyperbolic

variable (K : Type*) [CommRing K] (V : Type*) [AddCommGroup V] [Module K V] (L : Type*) [LieRing L] [LieAlgebra K L] [IsLieAbelian L]

def RealHyperbolicAux' : K →ₗ⁅K⁆ LieDerivation K L L :=
  LieHom.comp (Abelian.DerivationOfLinearMap K L) (LieHom.smulRight (LinearMap.id : End K L))

def RealHyperbolicAux : K →ₗ⁅K⁆ LieDerivation K (mkAbelian K V) (mkAbelian K V) := RealHyperbolicAux' K (mkAbelian K V)

/-- The almost abelian Lie algebra associated to real hyperbolic space, generalized to arbitrary `K`. -/
abbrev RealHyperbolic := K ⋉[RealHyperbolicAux K V] (mkAbelian K V)

/-- The almost abelian Lie algebra associated to real hyperbolic `n`-space, generalized to arbitrary `K`. -/
abbrev RealHyperbolic' (n : ℕ) (K : Type*) [CommRing K] := K ⋉[RealHyperbolicAux K (Fin (n - 1) → K)] (mkAbelian K (Fin (n - 1) → K))
--requires n > 0

@[inherit_doc]
notation "𝔥𝔶𝔭" => RealHyperbolic'

end liealghyperbolic

end LieAlgebra
