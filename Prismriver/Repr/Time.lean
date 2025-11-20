namespace Prismriver

class Time (I D : Type) [Add D] [HAdd I D I] [HSub I I D] [SMul Int D] [SMul D I] where
  zero : D

instance : Time Int Int where
  zero := 0
